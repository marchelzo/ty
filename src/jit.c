// jit.c - JIT compiler for ty

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <sys/mman.h>

#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#endif

#include "ty.h"
#include "value.h"
#include "ast.h"
#include "types.h"
#include "scope.h"
#include "class.h"
#include "jit.h"
#include "log.h"
#include "vm.h"
#include "compiler.h"
#include "str.h"
#include "array.h"
#include "dict.h"
#include "blob.h"
#include "queue.h"
#include "itable.h"
#include "compiler.h"

#define VALUE_SIZE (sizeof (Value))

// ============================================================================
// Value field offsets (must match struct value layout)
// ============================================================================
#define VAL_OFF_TYPE    offsetof(Value, type)    // u8 type
#define VAL_OFF_TAGS    offsetof(Value, tags)    // u16 tags
#define VAL_OFF_SRC     offsetof(Value, src)     // u16 src
#define VAL_OFF_Z       offsetof(Value, z)       // intmax_t z (for VALUE_INTEGER)
#define VAL_OFF_BOOL    offsetof(Value, boolean) // intmax_t z (for VALUE_INTEGER)
#define VAL_OFF_CLASS   offsetof(Value, class)   // u16 class (for VALUE_CLASS / VALUE_OBJECT)
#define VAL_OFF_OBJECT  offsetof(Value, object)  // void *object (for VALUE_OBJECT)
#define VAL_OFF_COUNT   offsetof(Value, count)   // i32 count (for VALUE_TUPLE)
#define VAL_OFF_ITEMS   offsetof(Value, items)   // Value *items (for VALUE_TUPLE)
#define VAL_OFF_REF     offsetof(Value, ref)     // Value *ref (for VALUE_REF)
#define VAL_OFF_REGEX   offsetof(Value, regex)   // Regex *regex (for VALUE_REGEX)
#define VAL_OFF_STR     offsetof(Value, str)     // u8 const *str (for VALUE_STRING)
#define VAL_OFF_BYTES   offsetof(Value, bytes)   // u32 bytes (for VALUE_STRING)
#define VAL_OFF_UOP     offsetof(Value, uop)
#define VAL_OFF_BOP     offsetof(Value, bop)

#define OFF_TY_STACK  offsetof(Ty, stack)
#define OFF_TY_ST     offsetof(Ty, st)
#define OFF_TY_TLS    offsetof(Ty, tls)
#define OFF_ST_FRAMES offsetof(co_state, frames)
#define OFF_ST_RC     offsetof(co_state, rc)
#define OFF_FRAME_FP  offsetof(Frame, fp)
#define OFF_VEC_DATA  offsetof(ValueVector, items)
#define OFF_VEC_LEN   offsetof(ValueVector, count)

// TyObject layout:
#define OBJ_OFF_INIT    0    // bool init
#define OBJ_OFF_NSLOT   4    // u32 nslot
#define OBJ_OFF_CLASS   8    // Class *class
#define OBJ_OFF_DYN     offsetof(TyObject, dynamic) // struct itable *dynamic
#define OBJ_OFF_SLOTS   offsetof(TyObject, slots)   // Value slots[] (flexible array)

// ============================================================================
// DynASM runtime includes
// ============================================================================

#include "../LuaJIT/dynasm/dasm_proto.h"

#if defined(__aarch64__) || defined(_M_ARM64)
#  include "../LuaJIT/dynasm/dasm_arm64.h"
#  include "jit_arm64.h"
#  define JIT_ARCH_ARM64 1
#  define PARAM_REG_BASE 0
#  define SCRATCH_REG_BASE 8
#  define MAX_SCRATCH_REGS 8
#elif defined(__x86_64__) || defined(_M_X64)
#  include "../LuaJIT/dynasm/dasm_x86.h"
#  include "jit_x64.h"
#  define JIT_ARCH_X64 1
static int const x64_param_regs[] = { 7, 6, 2, 1 };
#  define PARAM_REG(i) x64_param_regs[i]
#  define SCRATCH_REG_BASE 8
#  define MAX_SCRATCH_REGS 4
// x64 C calling convention arg registers
#  define X64_ARG0 7   // rdi
#  define X64_ARG1 6   // rsi
#  define X64_ARG2 2   // rdx
#  define X64_ARG3 1   // rcx
#else
#  define JIT_ARCH_NONE 1
#endif
#if defined(TY_NO_JIT) || defined(JIT_ARCH_NONE)
void jit_init(Ty *ty) { (void)ty; }
void jit_free(Ty *ty) { (void)ty; }
JitInfo *jit_compile(Ty *ty, Value const *func) { (void)ty; (void)func; return NULL; }
#else

// JIT trampoline offsets
#define OFF_JIT_RESUME    offsetof(Ty, jit.idx)
#define OFF_JIT_STATUS    offsetof(Ty, jit.status)
#define OFF_JIT_SAVED_RES offsetof(Ty, jit._idx)
#define OFF_JIT_PEND_FN   offsetof(Ty, jit._fn)
#define OFF_JIT_PEND_ENV  offsetof(Ty, jit._env)

// ============================================================================
// Fast-path statistics (enabled by TY_PROFILER / make PROF=1)
// ============================================================================

#ifdef TY_PROFILER
static struct {
        _Atomic u64 member_fast;
        _Atomic u64 member_slow;
        _Atomic u64 member_set_fast;
        _Atomic u64 member_set_slow;
        _Atomic u64 self_member_read_fast;
        _Atomic u64 self_member_read_slow;
        _Atomic u64 self_member_write_fast;
        _Atomic u64 self_member_write_slow;
        _Atomic u64 call_method_baked;
        _Atomic u64 call_method_builtin;
        _Atomic u64 call_method_slow;
        _Atomic u64 jeq_int;
        _Atomic u64 jeq_str;
        _Atomic u64 jeq_nil;
        _Atomic u64 jeq_slow;
        _Atomic u64 jcmp_int;
        _Atomic u64 jcmp_slow;
} jit_stats;

// ============================================================================
// Per-site slow path tracking
// ============================================================================
enum {
        SLOW_MEMBER_ACCESS,
        SLOW_MEMBER_SET,
        SLOW_SELF_MEMBER_READ,
        SLOW_SELF_MEMBER_WRITE,
        SLOW_CALL_METHOD,
        SLOW_JEQ,
        SLOW_JCMP,
        SLOW_KIND_COUNT
};

static char const *slow_kind_names[] = {
        [SLOW_MEMBER_ACCESS]     = "member_access",
        [SLOW_MEMBER_SET]        = "member_set",
        [SLOW_SELF_MEMBER_READ]  = "self_member_read",
        [SLOW_SELF_MEMBER_WRITE] = "self_member_write",
        [SLOW_CALL_METHOD]       = "call_method",
        [SLOW_JEQ]               = "eq/ne",
        [SLOW_JCMP]              = "cmp",
};

#define SLOW_TABLE_SIZE  4906   /* must be power of 2 */
#define SLOW_MAX_TYPES   16     /* top operand types tracked per site */
#define SLOW_PROBE_LIMIT 16

typedef struct {
        char const *ip;        /* bytecode IP (NULL = empty slot) */
        u8 kind;
        _Atomic u64 count;
        struct {
                i32 class_id;
                _Atomic u64 count;
        } types[SLOW_MAX_TYPES];
} SlowPathSite;

static SlowPathSite slow_table[SLOW_TABLE_SIZE];

// ============================================================================
// JIT compilation tracking
// ============================================================================

typedef struct {
        char const *name;
        char const *class_name;
        Expr const *expr;
        usize native_size;
        u64 compile_time_ns;
        int bc_code_size;
} JitCompileRecord;

static vec(JitCompileRecord) jit_compile_log = {0};
static u64 jit_total_compile_ns = 0;
static usize jit_total_native_bytes = 0;
static TySpinLock JitLogMutex;

inline static u64
jit_wall_time(void)
{
        struct timespec t;
        clock_gettime(CLOCK_MONOTONIC, &t);
        return 1000000000ULL * t.tv_sec + t.tv_nsec;
}

static int
jit_compile_cmp(void const *a, void const *b)
{
        u64 ta = ((JitCompileRecord const *)a)->compile_time_ns;
        u64 tb = ((JitCompileRecord const *)b)->compile_time_ns;
        return (tb > ta) - (tb < ta);
}

static inline void
slow_record_type(SlowPathSite *s, int class_id)
{
        /* Find existing or empty slot in the small type array */
        int empty = -1;
        u64 min_count = UINT64_MAX;
        int min_idx = 0;

        for (int i = 0; i < SLOW_MAX_TYPES; ++i) {
                u64 c = s->types[i].count;
                if (c == 0) {
                        if (empty < 0) empty = i;
                        continue;
                }
                if (s->types[i].class_id == class_id) {
                        ++s->types[i].count;
                        return;
                }
                if (c < min_count) {
                        min_count = c;
                        min_idx = i;
                }
        }

        if (empty >= 0) {
                s->types[empty].class_id = class_id;
                s->types[empty].count = 1;
        } else {
                /* Evict least-frequent */
                s->types[min_idx].class_id = class_id;
                s->types[min_idx].count = 1;
        }
}

static void
slow_record(Ty *ty, char const *ip, int kind, Value const *v1, Value const *v2)
{
        (void)ty;
        uptr h = (((uptr)ip >> 2) * 2654435761u) & (SLOW_TABLE_SIZE - 1);

        for (int i = 0; i < SLOW_PROBE_LIMIT; ++i) {
                SlowPathSite *s = &slow_table[(h + i) & (SLOW_TABLE_SIZE - 1)];

                if (s->ip == ip && s->kind == (u8)kind) {
                        ++s->count;
                        if (v1) slow_record_type(s, ClassOf(v1));
                        if (v2) slow_record_type(s, ClassOf(v2));
                        return;
                }

                if (s->ip == NULL) {
                        s->ip = ip;
                        s->kind = (u8)kind;
                        s->count = 1;
                        if (v1) slow_record_type(s, ClassOf(v1));
                        if (v2) slow_record_type(s, ClassOf(v2));
                        return;
                }
        }
        /* Table full at this bucket — just drop */
}

/* Callable from JIT: record slow path with 1 operand */
static void
jit_rt_slow1(Ty *ty, char const *ip, int kind, Value const *v)
{
        slow_record(ty, ip, kind, v, NULL);
}

/* Callable from JIT: record slow path with 2 operands */
static void
jit_rt_slow2(Ty *ty, char const *ip, int kind, Value const *a, Value const *b)
{
        slow_record(ty, ip, kind, a, b);
}

/* Thread-local bytecode IP for call_method slow path recording.
 * Set by JIT before calling runtime helpers that use all 6 register args. */
static _Thread_local char const *jit_stats_call_ip;

static void
jit_rt_set_call_ip(char const *ip)
{
        jit_stats_call_ip = ip;
}

static int
slow_cmp(void const *a, void const *b)
{
        u64 ca = ((SlowPathSite const *)a)->count;
        u64 cb = ((SlowPathSite const *)b)->count;
        return (cb > ca) - (cb < ca);
}

static void
fmt_size(char *buf, usize sz, usize bytes)
{
        if (bytes >= 1024 * 1024)
                snprintf(buf, sz, "%.1f MB", bytes / (1024.0 * 1024.0));
        else if (bytes >= 1024)
                snprintf(buf, sz, "%.1f KB", bytes / 1024.0);
        else
                snprintf(buf, sz, "%zu B", bytes);
}

static void
fmt_time(char *buf, usize sz, u64 ns)
{
        if (ns >= 1000000000ULL)
                snprintf(buf, sz, "%.2f s", ns / 1e9);
        else if (ns >= 1000000ULL)
                snprintf(buf, sz, "%.2f ms", ns / 1e6);
        else if (ns >= 1000ULL)
                snprintf(buf, sz, "%.1f us", ns / 1e3);
        else
                snprintf(buf, sz, "%llu ns", (unsigned long long)ns);
}

static void
pct_bar(FILE *out, double pct, int width)
{
        char const *color;

        if (pct >= 99.0)      color = PTERM(92);
        else if (pct >= 95.0) color = PTERM(32);
        else if (pct >= 80.0) color = PTERM(93);
        else if (pct >= 50.0) color = PTERM(33);
        else                  color = PTERM(91);

        int filled = (int)(pct / 100.0 * width + 0.5);
        if (filled > width) filled = width;

        fprintf(out, "%s", color);
        for (int i = 0; i < filled; ++i) fputc('|', out);
        fprintf(out, "%s", PTERM(0));
        for (int i = filled; i < width; ++i) fputc(' ', out);
}

static void
fast_path_row(FILE *out, char const *label, u64 fast, u64 slow)
{
        u64 total = fast + slow;
        if (total == 0) return;
        double pct = 100.0 * fast / total;

        fprintf(out, "   %-20s %12llu  %12llu   %s%5.1f%%%s  ",
                label,
                (unsigned long long)fast,
                (unsigned long long)slow,
                pct >= 95.0 ? PTERM(92) : pct >= 80.0 ? PTERM(93) : PTERM(91),
                pct,
                PTERM(0));
        pct_bar(out, pct, 20);
        fputc('\n', out);
}

void
jit_stats_report(Ty *ty, FILE *out)
{
        /* ====== Section 1: JIT compilation summary ====== */
        TySpinLockLock(&JitLogMutex);
        int ncompiled = vN(jit_compile_log);

        if (ncompiled > 0) {
                char time_buf[32], size_buf[32];
                fmt_time(time_buf, sizeof time_buf, jit_total_compile_ns);
                fmt_size(size_buf, sizeof size_buf, jit_total_native_bytes);

                fprintf(out, "%s======= JIT summary =======%s\n\n",
                        PTERM(95), PTERM(0));

                fprintf(out, "   Compiled: %s%d%s functions  (%s%s%s compile time, %s%s%s native code)\n\n",
                        PTERM(1), ncompiled, PTERM(0),
                        PTERM(93), time_buf, PTERM(0),
                        PTERM(93), size_buf, PTERM(0));

                /* Sort by compile time descending */
                qsort(vv(jit_compile_log), ncompiled,
                      sizeof(JitCompileRecord), jit_compile_cmp);

                fprintf(out, "   %s%-4s  %-36s %8s  %8s  %5s  %9s%s\n",
                        PTERM(90),
                        "#", "Function", "BC", "Native", "Ratio", "Compile",
                        PTERM(0));

                int show = ncompiled < 20 ? ncompiled : 20;
                for (int i = 0; i < show; ++i) {
                        JitCompileRecord *r = &vv(jit_compile_log)[i];
                        char tbuf[32], nbuf[32], bbuf[32];
                        fmt_time(tbuf, sizeof tbuf, r->compile_time_ns);
                        fmt_size(nbuf, sizeof nbuf, r->native_size);
                        fmt_size(bbuf, sizeof bbuf, r->bc_code_size);

                        double ratio = r->bc_code_size > 0
                                ? (double)r->native_size / r->bc_code_size
                                : 0.0;

                        char fname[48];
                        if (r->class_name[0])
                                snprintf(fname, sizeof fname, "%s.%s", r->class_name, r->name);
                        else
                                snprintf(fname, sizeof fname, "%s", r->name);

                        fprintf(out, "   %s%-4d%s  %s%-36s%s %8s  %8s  %s%4.1fx%s  %9s\n",
                                PTERM(90), i + 1, PTERM(0),
                                PTERM(34), fname, PTERM(0),
                                bbuf, nbuf,
                                ratio > 6.0 ? PTERM(91) : ratio > 3.0 ? PTERM(93) : PTERM(92),
                                ratio, PTERM(0),
                                tbuf);
                }

                if (ncompiled > show) {
                        fprintf(out, "   %s... and %d more%s\n", PTERM(90), ncompiled - show, PTERM(0));
                }

                fputc('\n', out);
        }

        TySpinLockUnlock(&JitLogMutex);

        /* ====== Section 2: Fast-path stats ====== */
        u64 slow_totals[SLOW_KIND_COUNT] = {0};
        for (int i = 0; i < SLOW_TABLE_SIZE; ++i) {
                if (slow_table[i].ip != NULL && slow_table[i].count > 0) {
                        slow_totals[slow_table[i].kind] += slow_table[i].count;
                }
        }

        slow_totals[SLOW_MEMBER_ACCESS] += jit_stats.member_slow;
        slow_totals[SLOW_MEMBER_SET]    += jit_stats.member_set_slow;
        slow_totals[SLOW_CALL_METHOD]   += jit_stats.call_method_slow;

        u64 total_fast = jit_stats.member_fast + jit_stats.member_set_fast
                       + jit_stats.self_member_read_fast + jit_stats.self_member_write_fast
                       + jit_stats.call_method_baked + jit_stats.call_method_builtin
                       + jit_stats.jeq_int + jit_stats.jeq_str + jit_stats.jeq_nil
                       + jit_stats.jcmp_int;
        u64 total_slow = 0;
        for (int i = 0; i < SLOW_KIND_COUNT; ++i) total_slow += slow_totals[i];

        if (total_fast + total_slow > 0) {
                fprintf(out, "%s======= JIT fast paths =======%s\n\n",
                        PTERM(95), PTERM(0));

                fprintf(out, "   %s%-20s %12s  %12s   %6s%s\n",
                        PTERM(90),
                        "Operation", "Fast", "Slow", "Fast %",
                        PTERM(0));

                fast_path_row(out, "member_access",     jit_stats.member_fast,            slow_totals[SLOW_MEMBER_ACCESS]);
                fast_path_row(out, "member_set",         jit_stats.member_set_fast,         slow_totals[SLOW_MEMBER_SET]);
                fast_path_row(out, "self_member_read",   jit_stats.self_member_read_fast,   slow_totals[SLOW_SELF_MEMBER_READ]);
                fast_path_row(out, "self_member_write",  jit_stats.self_member_write_fast,  slow_totals[SLOW_SELF_MEMBER_WRITE]);

                /* call_method has 3 categories, not a simple fast/slow */
                u64 cm_fast = jit_stats.call_method_baked + jit_stats.call_method_builtin;
                u64 cm_slow = slow_totals[SLOW_CALL_METHOD];
                if (cm_fast + cm_slow > 0) {
                        double pct = 100.0 * cm_fast / (cm_fast + cm_slow);
                        fprintf(out, "   %-20s %s%12llu%s  %12llu   %s%5.1f%%%s  ",
                                "call_method",
                                PTERM(34),
                                (unsigned long long)cm_fast,
                                PTERM(0),
                                (unsigned long long)cm_slow,
                                pct >= 95.0 ? PTERM(92) : pct >= 80.0 ? PTERM(93) : PTERM(91),
                                pct,
                                PTERM(0));
                        pct_bar(out, pct, 20);
                        fprintf(out, "\n      %sbaked=%llu  builtin=%llu%s\n",
                                PTERM(90),
                                (unsigned long long)jit_stats.call_method_baked,
                                (unsigned long long)jit_stats.call_method_builtin,
                                PTERM(0));
                }

                fast_path_row(out, "eq/ne", jit_stats.jeq_int + jit_stats.jeq_str + jit_stats.jeq_nil, slow_totals[SLOW_JEQ]);
                if (jit_stats.jeq_int + jit_stats.jeq_str + jit_stats.jeq_nil + slow_totals[SLOW_JEQ] > 0) {
                        fprintf(out, "      %sint=%llu  str=%llu  nil=%llu%s\n",
                                PTERM(90),
                                (unsigned long long)jit_stats.jeq_int,
                                (unsigned long long)jit_stats.jeq_str,
                                (unsigned long long)jit_stats.jeq_nil,
                                PTERM(0));
                }

                fast_path_row(out, "cmp", jit_stats.jcmp_int, slow_totals[SLOW_JCMP]);

                fputc('\n', out);
        }

        /* ====== Section 3: Top slow-path sites ====== */
        SlowPathSite sorted[SLOW_TABLE_SIZE];
        int n = 0;
        for (int i = 0; i < SLOW_TABLE_SIZE; ++i) {
                if (slow_table[i].ip != NULL && slow_table[i].count > 0) {
                        sorted[n++] = slow_table[i];
                }
        }

        if (n > 0) {
                qsort(sorted, n, sizeof sorted[0], slow_cmp);

                int show = n < 20 ? n : 20;

                fprintf(out, "%s======= top slow-path sites =======%s\n\n",
                        PTERM(95), PTERM(0));

                for (int i = 0; i < show; ++i) {
                        SlowPathSite *s = &sorted[i];
                        Expr const *e = compiler_find_expr(ty, s->ip);

                        fprintf(out, "   %s%2d.%s  [%s%-18s%s] %s%8llu%s hits",
                                PTERM(90), i + 1, PTERM(0),
                                PTERM(34), slow_kind_names[s->kind], PTERM(0),
                                PTERM(1), (unsigned long long)s->count, PTERM(0));

                        if (e && e->mod && e->mod->path) {
                                fprintf(out, "  %s%s:%u:%u%s",
                                        PTERM(94),
                                        e->mod->path,
                                        e->start.line + 1,
                                        e->start.col + 1,
                                        PTERM(0));
                        }

                        fputc('\n', out);

                        /* Type breakdown on next line */
                        bool has_types = false;
                        for (int j = 0; j < SLOW_MAX_TYPES; ++j) {
                                if (s->types[j].count > 0) { has_types = true; break; }
                        }

                        if (has_types) {
                                fprintf(out, "       %stypes:%s ", PTERM(90), PTERM(0));
                                bool first = true;
                                for (int j = 0; j < SLOW_MAX_TYPES; ++j) {
                                        if (s->types[j].count == 0) continue;
                                        if (!first) fprintf(out, ", ");
                                        first = false;
                                        fprintf(out, "%s%s%s=%llu",
                                                PTERM(93),
                                                class_name(ty, s->types[j].class_id),
                                                PTERM(0),
                                                (unsigned long long)s->types[j].count);
                                }
                                fputc('\n', out);
                        }
                }

                fputc('\n', out);
        }
}

#define STAT(name) (++jit_stats.name)

static void jit_rt_stat_member_fast(void)            { STAT(member_fast); }
static void jit_rt_stat_member_set_fast(void)        { STAT(member_set_fast); }
static void jit_rt_stat_self_member_read_fast(void)  { STAT(self_member_read_fast); }
static void jit_rt_stat_self_member_write_fast(void) { STAT(self_member_write_fast); }
static void jit_rt_stat_jeq_int(void)                { STAT(jeq_int); }
static void jit_rt_stat_jeq_str(void)                { STAT(jeq_str); }
static void jit_rt_stat_jeq_nil(void)                { STAT(jeq_nil); }
static void jit_rt_stat_jcmp_int(void)               { STAT(jcmp_int); }

#define EMIT_STAT(fn_ptr) do {                                         \
        jit_emit_load_imm(asm, BC_CALL, (iptr)(fn_ptr));               \
        jit_emit_call_reg(asm, BC_CALL);                               \
} while (0)

/* Emit a slow-path record call with 1 operand: jit_rt_slow1(ty, ip, kind, v) */
#define EMIT_SLOW1(bc_ip, kind, val_reg, val_off) do {                           \
        jit_emit_mov(asm, BC_A0, BC_TY);                                         \
        jit_emit_load_imm(asm, BC_A1, (iptr)(bc_ip));                            \
        jit_emit_load_imm(asm, BC_A2, (kind));                                   \
        jit_emit_add_imm(asm, BC_A3, (val_reg), (val_off));                      \
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_slow1);                     \
        jit_emit_call_reg(asm, BC_CALL);                                         \
} while (0)

/* Emit a slow-path record call with 2 operands: jit_rt_slow2(ty, ip, kind, a, b) */
#define EMIT_SLOW2(bc_ip, kind, a_reg, a_off, b_reg, b_off) do {                     \
        jit_emit_mov(asm, BC_A0, BC_TY);                                             \
        jit_emit_load_imm(asm, BC_A1, (iptr)(bc_ip));                                \
        jit_emit_load_imm(asm, BC_A2, (kind));                                       \
        jit_emit_add_imm(asm, BC_A3, (a_reg), (a_off));                              \
        jit_emit_add_imm(asm, BC_A4, (b_reg), (b_off));                              \
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_slow2);                         \
        jit_emit_call_reg(asm, BC_CALL);                                             \
} while (0)

/* Store bytecode IP in TLS before calling a runtime helper that has no room for an IP arg */
#define EMIT_SET_CALL_IP(bc_ip) do {                                   \
        jit_emit_load_imm(asm, BC_A0, (iptr)(bc_ip));                  \
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_set_call_ip);     \
        jit_emit_call_reg(asm, BC_CALL);                               \
} while (0)

/* Record slow path in C runtime helpers (call_method paths) */
#define SLOW_RECORD(...) slow_record(__VA_ARGS__)

#else
#define STAT(name) ((void)0)
#define EMIT_STAT(fn_ptr) ((void)0)
#define EMIT_SLOW1(bc_ip, kind, val_reg, val_off) ((void)0)
#define EMIT_SLOW2(bc_ip, kind, a_reg, a_off, b_reg, b_off) ((void)0)
#define EMIT_SET_CALL_IP(bc_ip) ((void)0)
#define SLOW_RECORD(...) ((void)0)
#endif

#if JIT_RT_DEBUG
#define DBG(fmt, ...) do {                                                                  \
        jit_emit_mov(asm, BC_A0, BC_TY);                                                    \
        jit_emit_load_imm(asm, BC_A1, ctx->sp);                                             \
        jit_emit_load_imm(asm, BC_A2, ((iptr)xfmt(fmt __VA_OPT__(,) __VA_ARGS__)));         \
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_dbg);                                  \
        jit_emit_call_reg(asm, BC_CALL);                                                    \
} while (0)
#else
#define DBG(fmt, ...)
#endif

#define TOP_OF_STACK(v) (vN(ty->stack) = ((v) - vv(ty->stack)) + 1)

static void
jit_rt_dbg(Ty *ty, i64 sp, char const *msg)
{
        usize fp = vvL(ty->st.frames)->fp;
        usize bp = fp + vvL(ty->st.frames)->f.info[FUN_INFO_BOUND];
        Value const *v = v_(ty->stack, bp + sp - 1);

        char const *repr = (sp == 0) ? "<>" : SHOW(v, BASIC, ABBREV);

        XPRINT_CTX("%sJIT%s [%zu]: %s%s%s: %s", TERM(91), TERM(0), (usize)(bp + sp - 1 - fp), TERM(34), msg, TERM(0), repr);
}

static void
jit_rt_itrc(Ty *ty, i64 sp, char const *msg)
{

        //int fp = vvL(ty->st.frames)->fp;
        //int np = vvL(ty->st.frames)->f.info[FUN_INFO_PARAM_COUNT];
        //Value const *f = &vvL(ty->st.frames)->f;

        XPRINT_CTX("[jit] %s", msg);
}

static void
jit_rt_idbg(Ty *ty, i64 sp, char const *op)
{

        int fp = vvL(ty->st.frames)->fp;
        int np = vvL(ty->st.frames)->f.info[FUN_INFO_PARAM_COUNT];
        Value const *f = &vvL(ty->st.frames)->f;

        char *self;
        if (class_of(f) != -1) {
                self = SHOW(&vv(ty->stack)[fp + np], BASIC, ABBREV);
        } else {
                self = "<no self>";
        }

        XPRINT_CTX(
                "(%2d) %sJIT%s: %s%s%s   (self/frame[%d]=%s)",
                (int)sp,
                TERM(94),
                TERM(0),
                TERM(34;1),
                op,
                TERM(0),
                np,
                self
        );
}

static void
jit_rt_add(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z + b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        Value val = vm_2op(ty, OP_ADD, a, b);
        *v_(ty->stack, idx) = val;
}

static void
jit_rt_sub(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z - b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        Value val = vm_2op(ty, OP_SUB, a, b);
        *v_(ty->stack, idx) = val;
}

static void
jit_rt_mul(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z * b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        Value val = vm_2op(ty, OP_MUL, a, b);
        *v_(ty->stack, idx) = val;
}

static void
jit_rt_div(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                if (b->z == 0) ZeroDividePanic(ty);
                *result = INTEGER(a->z / b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        Value val = vm_2op(ty, OP_DIV, a, b);
        *v_(ty->stack, idx) = val;
}

static void
jit_rt_mod(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                if (b->z == 0) ZeroDividePanic(ty);
                *result = INTEGER(a->z % b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        Value val = vm_2op(ty, OP_MOD, a, b);
        *v_(ty->stack, idx) = val;
}

static void
jit_rt_neg(Ty *ty, Value *result, Value *a)
{
        (void)ty;
        if (a->type == VALUE_INTEGER) {
                *result = INTEGER(-a->z);
                return;
        }
        if (a->type == VALUE_REAL) {
                *result = REAL(-a->real);
                return;
        }
        zP("JIT -: unsupported operand: %s", SHOW(a));
}

static void
jit_rt_not(Ty *ty, Value *result, Value *a)
{
        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 1;
        Value val = BOOLEAN(!value_truthy(ty, a));
        *v_(ty->stack, idx) = val;
}

static void
jit_rt_eq(Ty *ty, Value *result, Value *a, Value *b)
{
        if (LIKELY(a->type == VALUE_NIL || b->type == VALUE_NIL)) {
                *result = BOOLEAN(a->type == b->type);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        Value val = BOOLEAN(value_test_equality(ty, a, b));
        *v_(ty->stack, idx) = val;
}

static void
jit_rt_ne(Ty *ty, Value *result, Value *a, Value *b)
{
        if (LIKELY(a->type == VALUE_NIL || b->type == VALUE_NIL)) {
                *result = BOOLEAN(a->type != b->type);
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        Value val = BOOLEAN(!value_test_equality(ty, a, b));
        *v_(ty->stack, idx) = val;
}

static int
jit_rt_str_eq(Value *a, Value *b)
{
        return (a->bytes == b->bytes)
            && (memcmp(a->str, b->str, a->bytes) == 0);
}

static void
jit_rt_lt(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z < b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        DoLt(ty);
}

static void
jit_rt_le(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z <= b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        DoLeq(ty);
}

static void
jit_rt_gt(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z > b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        DoGt(ty);
}

static void
jit_rt_ge(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z >= b->z);
                return;
        }

        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 2;

        DoGeq(ty);
}

static void
jit_rt_dbg_self(Ty *ty, Value *self, int m_id)
{
        LOGX(
                "JIT: Debug self member access: self=%s, member_id=%d (%s)",
                SHOW(self, BASIC, ABBREV),
                m_id,
                M_NAME(m_id)
        );

        Class *cls = class_get(ty, self->class);

        if (!cls->final) {
                LOGX("  Class is not final, cannot use fast path");
                return;
        }

        if (!self->object->init) {
                LOGX("  Object is not initialized, cannot use fast path");
                return;
        }

        if (m_id < vN(cls->offsets_r)) {
                u16 off = v__(cls->offsets_r, m_id);
                if (off != OFF_NOT_FOUND) {
                        u8 kind = (off >> OFF_SHIFT);
                        if (kind == OFF_FIELD) {
                                LOGX(
                                        "  Fast path: field at offset %d, value=%s",
                                        off & OFF_MASK,
                                        SHOW(&self->object->slots[off & OFF_MASK], BASIC, ABBREV)
                                );
                                return;
                        }
                }
        }

        LOGX("  Slow path: member not found or not a field");
}

static void
jit_rt_member(Ty *ty, Value *result, Value *obj, int member_id)
{
        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 1;

        if (obj == NULL) {
                obj = vm_get_self(ty);
                v_L(ty->stack) = *obj;
        }

        if (obj->type == VALUE_OBJECT) {
                Class *cls = class_get(ty, obj->class);
                if (member_id < vN(cls->offsets_r)) {
                        u16 off = v__(cls->offsets_r, member_id);
                        if (off != OFF_NOT_FOUND) {
                                u8 kind = (off >> OFF_SHIFT);
                                if (kind == OFF_FIELD) {
                                        STAT(member_fast);
                                        *result = obj->object->slots[off & OFF_MASK];
                                        return;
                                }
                        }
                }
        }

        STAT(member_slow);

        Value v = GetMember(ty, member_id, true, true);
        if (UNLIKELY(v.type == VALUE_NONE)) {
                v = NIL;
        }

        *v_(ty->stack, idx) = v;
}

#define JIT_RT_MUT_OP(op, vm_op)                                                          \
        static void                                                                       \
        jit_rt_mut_##op(Ty *ty, Value *target, Value *val, Value *result)                 \
        {                                                                                 \
                ptrdiff_t idx = result - vv(ty->stack);                                   \
                vN(ty->stack) = val - vv(ty->stack) + 1;                                  \
                vm_jit_push_target(ty, target);                                           \
                vm_op(ty, true);                                                          \
                *v_(ty->stack, idx) = *vm_get(ty, 0);                                     \
        }                                                                                 \
                                                                                          \
        static void                                                                       \
        jit_rt_member_mut_##op(Ty *ty, Value *obj, int m_id, Value *val, Value *result)   \
        {                                                                                 \
                ptrdiff_t idx = result - vv(ty->stack);                                   \
                vN(ty->stack) = val - vv(ty->stack) + 1;                                  \
                DoTargetMember(ty, *obj, m_id);                                           \
                vm_op(ty, true);                                                          \
                *v_(ty->stack, idx) = *vm_get(ty, 0);                                     \
        }                                                                                 \
        static void                                                                       \
        jit_rt_subscript_mut_##op(Ty *ty, Value *val, Value *xs, Value *ix)               \
        {                                                                                 \
                ptrdiff_t idx = val - vv(ty->stack);                                      \
                vN(ty->stack) = val - vv(ty->stack) + 1;                                  \
                xvP(ty->stack, *xs);                                                      \
                xvP(ty->stack, *ix);                                                      \
                DoTargetSubscript(ty);                                                    \
                vm_op(ty, true);                                                          \
                *v_(ty->stack, idx) = *vm_get(ty, 0);                                     \
        }


JIT_RT_MUT_OP(add, DoMutAdd)
JIT_RT_MUT_OP(sub, DoMutSub)
JIT_RT_MUT_OP(mul, DoMutMul)
JIT_RT_MUT_OP(div, DoMutDiv)
JIT_RT_MUT_OP(mod, DoMutMod)
JIT_RT_MUT_OP(and, DoMutAnd)
JIT_RT_MUT_OP(or,  DoMutOr)
JIT_RT_MUT_OP(xor, DoMutXor)
JIT_RT_MUT_OP(shl, DoMutShl)
JIT_RT_MUT_OP(shr, DoMutShr)


static void
jit_rt_member_set(Ty *ty, Value *obj, int member_id, Value *val)
{
        STAT(member_set_slow);
        vN(ty->stack) = val - vv(ty->stack) + 1;
        if (obj == NULL) {
                obj = vm_get_self(ty);
        }
        DoTargetMember(ty, *obj, member_id);
        DoAssignExec(ty);
}

static int
jit_rt_try_tag_pop(Ty *ty, Value *val, int tag)
{
        return TryUnwrap(val, tag);
}

static void
jit_rt_render_template(Ty *ty, Value *result, uptr expr_ptr)
{
        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx;
        Value val = compiler_render_template(ty, (Expr *)expr_ptr);
        *v_(ty->stack, idx) = val;
}

static int
jit_rt_index_tuple(Value *tos, Value *dst, int i)
{
        if (tos->type != VALUE_TUPLE || tos->count <= i) {
                return 0;
        }
        *dst = tos->items[i];
        return 1;
}

static int
jit_rt_try_tuple_member(Value *tos, Value *dst, bool required, int name_id)
{
        if (tos->type != VALUE_TUPLE) {
                return 0;
        }

        if (tos->ids != NULL) {
                for (int i = 0; i < tos->count; ++i) {
                        if (tos->ids[i] == name_id) {
                                *dst = tos->items[i];
                                return 1;
                        }
                }
        }

        if (!required) {
                *dst = NIL;
                return 1;
        }

        return 0;
}

static int
jit_rt_try_steal_tag(Ty *ty, Value *tos, Value *target)
{
        if (tos->tags > 0) {
                *target = TAG(tags_first(ty, tos->tags));
                (PopTag)(ty, tos);
                return 1;
        }

        return 0;
}

static int
jit_rt_jii(Ty *ty, Value *v, int class_id)
{
        return class_is_subclass(ty, ClassOf(v), class_id);
}

static void
jit_rt_capture(Ty *ty, Value *local, Value **env, int env_idx)
{
        Value *vp = uAo(sizeof (Value), GC_VALUE);
        *vp = *local;
        *local = REF(vp);
        env[env_idx] = vp;
}

static char const *
jit_rt_function(Ty *ty, Value *result, char const *ip, int bound_caps)
{
        Value v = {0};

        ip = ALIGNED_FOR(i64, ip);

        v.type = VALUE_FUNCTION;
        v.info = (i32 *)ip;

        int hs   = v.info[FUN_INFO_HEADER_SIZE];
        int size = v.info[FUN_INFO_CODE_SIZE];
        int nEnv = v.info[FUN_INFO_CAPTURES];

        int ncaps = (bound_caps > 0) ? nEnv - bound_caps : nEnv;

        if (from_eval(&v)) {
                v.info = mAo(hs + size, GC_ANY);
                memcpy(v.info, ip, hs + size);
        }

        ip += size + hs;

        if (nEnv > 0) {
                v.env = uAo0(nEnv * sizeof (Value *), GC_ENV);
        }

        for (int i = 0; i < ncaps; ++i) {
                bool b;
                int j;
                memcpy(&b, ip, sizeof b); ip += sizeof b;
                memcpy(&j, ip, sizeof j); ip += sizeof j;
                Value *p = vm_jit_pop_target(ty);
                if (b) {
                        if (p->type == VALUE_REF) {
                                v.env[j] = p->ptr;
                        } else {
                                Value *new = uAo(sizeof (Value), GC_VALUE);
                                *new = *p;
                                *p = REF(new);
                                v.env[j] = new;
                        }
                } else {
                        v.env[j] = p;
                }
        }

        *result = v;

        return ip;
}

static void
jit_rt_bind_instance(Ty *ty, Value *result, int n, int z)
{
        Value *vp;
        if (n < 0) {
                vp = class_lookup_method_i(ty, -n, z);
                *result = vm_jit_bind_method(ty, vp, result);
        } else {
                u16 off = OFF_NOT_FOUND;
                if (result->type == VALUE_OBJECT) {
                        Class *c = class_get(ty, n);
                        if (z < vN(c->offsets_r)) {
                                off = v__(c->offsets_r, z);
                        }
                }
                if (off == OFF_NOT_FOUND) {
                        vp = class_lookup_method_i(ty, n, z);
                        *result = vm_jit_bind_method(ty, vp, result);
                } else {
                        switch (off >> OFF_SHIFT) {
                        case OFF_METHOD:
                                vp = v_(class_get(ty, n)->methods.values, off & OFF_MASK);
                                break;
                        case OFF_METHOD_X:
                                vp = &result->object->slots[off & OFF_MASK];
                                break;
                        default:
                                return;
                        }
                        *result = vm_jit_bind_method(ty, vp, result);
                }
        }
}

static int
jit_rt_ensure_equals_var(Ty *ty, Value *a, Value *b)
{
        return value_test_equality(ty, a, b);
}

static int
jit_rt_try_index(Value *tos, Value *dst, int i, bool required)
{
        if (tos->type != VALUE_ARRAY) {
                return 0;
        }

        int idx = i;
        if (idx < 0) {
                idx += vN(*tos->array);
        }

        if (vN(*tos->array) <= idx) {
                if (required) {
                        return 0;
                } else {
                        *dst = NIL;
                        return 1;
                }
        }

        *dst = v__(*tos->array, idx);

        return 1;
}

static void
jit_rt_tuple(Ty *ty, Value *top, i32 n, i32 *ids)
{
        vN(ty->stack) = top - vv(ty->stack);

        Value *items = mAo(n * sizeof (Value), GC_TUPLE);
        Value tuple = TUPLE(items, ids, n, false);

        memcpy(items, vZ(ty->stack) - n, n * sizeof (Value));
        vN(ty->stack) -= n;

        xvP(ty->stack, tuple);
}

static void
jit_rt_subscript(Ty *ty, Value *top)
{
        ptrdiff_t idx = (top - vv(ty->stack));
        vN(ty->stack) = idx + 2;
        DoSubscript(ty, true);
}

static int
jit_rt_truthy(Ty *ty, Value *v)
{
        return value_truthy(ty, v);
}

static void
jit_rt_bit_and(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_AND, true);
}

static void
jit_rt_bit_or(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_OR, true);
}

static void
jit_rt_bit_xor(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_XOR, true);
}

static void
jit_rt_shl(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_SHL, true);
}

static void
jit_rt_shr(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_SHR, true);
}

// Increment a Value in-place (mirrors static IncValue in vm.c)
static void
jit_rt_inc(Ty *ty, Value *v)
{
        TOP_OF_STACK(v);
        IncValue(ty, v);
}

// Decrement a Value in-place (mirrors static DecValue in vm.c)
static void
jit_rt_dec(Ty *ty, Value *v)
{
        TOP_OF_STACK(v);
        DecValue(ty, v);
}

// String literal: mirrors static DoStringLiteral in vm.c
static void
jit_rt_string(Ty *ty, Value *result, i32 i)
{
        InternEntry const *interned = intern_entry(&xD.strings, i);
        *result = STRING_NOGC(interned->name, (uptr)interned->data);
}

// Three-way compare => Value (wraps value_compare into INTEGER)
static void
jit_rt_cmp(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(ty->stack));
        vN(ty->stack) = idx + 2;
        DoCmp(ty);
}

// Count (#v) => Value
static void
jit_rt_count(Ty *ty, Value *result, Value *v)
{
        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + 1;
        DoCount(ty, true);
}

static void
jit_rt_tls0(Ty *ty, Value *top, int n)
{
        vN(ty->stack) = top - vv(ty->stack);

        while (vN(ty->tls) <= n) {
                xvP(ty->tls, NONE);
        }

        vm_exec(ty, v__(xD.tls0, n));
}

// Subscript assign: container[subscript] = value
// Stack layout: value, container, subscript (TOS)
// Pops all 3
static void
jit_rt_assign_subscript(Ty *ty, Value *value, Value *container, Value *subscript)
{
        vN(ty->stack) = value - vv(ty->stack) + 3;
        DoAssignSubscript(ty, true);
}

// Create array from N values on the JIT operand stack
static void
jit_rt_array(Ty *ty, Value *result, Value *elements, int n)
{
        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + n;
        Array *xs = vAn(n);
        vN(*xs) = n;
        memcpy(vv(*xs), v_(ty->stack, idx), n * sizeof (Value));
        *v_(ty->stack, idx) = ARRAY(xs);
}

// Create empty array
static void
jit_rt_array0(Ty *ty, Value *result)
{
        *result = ARRAY(uAo0(sizeof (Array), GC_ARRAY));
}


static void
jit_rt_array_compr(Ty *ty, Value *top, i32 idx, i32 n)
{
        vN(ty->stack) = top - vv(ty->stack);
        Value *array = vZ(ty->stack) - (idx + n + 1);
        vvPn(*array->array, vZ(ty->stack) - n, n);
        vN(ty->stack) -= n;
}

// CALL_STATIC_METHOD: push CLASS value as self, then CallMethod
static void
jit_rt_call_static_method(Ty *ty, Value *result, int class_id, int argc, int method_id, int nkw)
{
        ptrdiff_t idx = result - vv(ty->stack);
        vN(ty->stack) = idx + argc;
        xvP(ty->stack, CLASS(class_id));
        CallMethod(ty, method_id, argc, nkw, true, true);
        *result = *vm_pop(ty);
}

static void
jit_rt_default_dict(Ty *ty, Value *top, i32 n)
{
        ptrdiff_t idx = top - vv(ty->stack);
        vN(ty->stack) = idx;
        Value dflt = vXx(ty->stack);
        DoDictLiteral(ty, n, &dflt);
}

static void
jit_rt_dict(Ty *ty, Value *top, i32 n)
{
        ptrdiff_t idx = top - vv(ty->stack);
        vN(ty->stack) = idx;
        DoDictLiteral(ty, n, NULL);
}

// LOOP_ITER: push SENTINEL, RC=0, IterGetNext
static void
jit_rt_loop_iter(Ty *ty, Value *top)
{
        TOP_OF_STACK(top - 1);
        vm_jit_loop_iter(ty);
}

// LOOP_CHECK: returns true if loop is done (NONE detected)
static int
jit_rt_loop_check(Ty *ty, int z, Value *top)
{
        TOP_OF_STACK(top);
        return vm_jit_loop_check(ty, z);
}

// THROW: raise exception
static void
jit_rt_throw(Ty *ty, Value *exc)
{
        ptrdiff_t idx = (exc - vv(ty->stack));
        vN(ty->stack) = idx + 1;
        vm_throw(ty, exc);
}

// BAD_MATCH: tag TOS with MatchError and throw
static void
jit_rt_bad_match(Ty *ty, Value *v)
{
        v->tags = tags_push(ty, v->tags, TAG_MATCH_ERR);
        v->type |= VALUE_TAGGED;
        vm_throw(ty, v);
}

// RANGE: create a range object
static void
jit_rt_range(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(ty->stack));
        vN(ty->stack) = idx + 2;
        Value val = vm_make_range(ty, a, b, false);
        *v_(ty->stack, idx) = val;
}

// INCRANGE: create an inclusive range object
static void
jit_rt_incrange(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(ty->stack));
        vN(ty->stack) = idx + 2;
        Value val = vm_make_range(ty, a, b, true);
        *v_(ty->stack, idx) = val;
}

// TO_STRING: convert value to string
static void
jit_rt_to_string(Ty *ty, Value *val)
{
        if (val->type == VALUE_STRING) {
                return;
        }

        if (UNLIKELY(val->type == VALUE_PTR)) {
                char *show = VSC(val);
                *val = STRING_NOGC(show, strlen(show));
                return;
        }

        ptrdiff_t idx = (val - vv(ty->stack));
        vN(ty->stack) = idx + 1;
        CallMethod(ty, NAMES._str_, 0, 0, false, true);
}

// ASSIGN_GLOBAL: set global[n] = value
static void
jit_rt_assign_global(Ty *ty, int n, Value *val)
{
        *vm_global(ty, n) = *val;
}

#if JIT_ARCH_ARM64
// ARM64 callee-saved register assignments
#define BC_TY    19   // x19
#define BC_RES   20   // x20
#define BC_LOC   21   // x21
#define BC_ENV   22   // x22
#define BC_OPS   23   // x23
// Scratch registers (caller-saved, trashed by helper calls)
#define BC_S0    8    // x8
#define BC_S1    9    // x9
#define BC_S2   10    // x10
#define BC_S3   11    // x11
#define BC_CALL 16    // x16 - call target / scratch
// C calling convention argument registers
#define BC_A0  0    // x0
#define BC_A1  1    // x1
#define BC_A2  2    // x2
#define BC_A3  3    // x3
#define BC_A4  4    // x4
#define BC_A5  5    // x5
#define BC_RET 0    // x0 - return value register
#elif JIT_ARCH_X64
// x86-64 callee-saved register assignments
#define BC_TY    12   // r12
#define BC_RES   13   // r13
#define BC_LOC   14   // r14
#define BC_ENV   15   // r15
#define BC_OPS    3   // rbx
// Scratch registers (caller-saved, trashed by helper calls)
#define BC_S0    8    // r8
#define BC_S1    9    // r9
#define BC_S2   10    // r10
#define BC_S3   11    // r11
#define BC_CALL 10    // r10 - call target / scratch (aliases BC_S2)
// C calling convention argument registers (System V AMD64 ABI)
#define BC_A0  7    // rdi
#define BC_A1  6    // rsi
#define BC_A2  2    // rdx
#define BC_A3  1    // rcx
#define BC_A4  8    // r8  (aliases BC_S0, fine before call)
#define BC_A5  9    // r9  (aliases BC_S1, fine before call)
#define BC_RET 0    // rax - return value register
#endif

// Pack two 32-bit ints into a single 64-bit immediate for register-only calls
#define PACK32(hi, lo) (((i64)(hi) << 32) | ((i64)(u32)(lo)))

#define MAX_BC_OPS    64   // Max operand stack depth
#define MAX_BC_LABELS 512  // Max DynASM labels

// Bytecode compilation context
typedef struct {
        dasm_State *asm;
        Ty *ty;
        Value const *func;
        int sp;             // Current operand stack depth (compile-time)
        int max_sp;         // Maximum operand stack depth seen
        int next_label;
        int label_capacity;
        int param_count;
        int bound;
        char const *name;

        // Type information (from expr_of(func)->_type)
        Type *func_type;    // TYPE_FUNCTION with param types and return type
        Class *self_class;  // Non-NULL if this is a method (class of self)
        int self_class_id;  // Class ID for guard checks (-1 if unknown)

        int save_sp_stack[16]; // Stack of saved sp values for SAVE_STACK_POS
        bool save_sp_divergent[16]; // Whether branches caused divergent sp since SAVE_STACK_POS
        int save_sp_top;       // Top of save_sp stack (-1 = empty)
        char const *last_op;   // DEBUG: last opcode name for bail diagnostics

        // Track which local each operand stack slot came from (-1 = unknown)
        // Used to look up types for CALL_METHOD/MEMBER_ACCESS fast paths
        Type *op_types[MAX_BC_OPS];

        // Label map: bytecode offset => DynASM label + expected sp + save_sp state
        struct {
                int offset;
                int label;
                int sp;
                int save_sp_top;
                int save_sp_stack[16];
        } labels[MAX_BC_LABELS];

        // Compile-time target tracking for MUT_ADD/MUT_SUB fusion
        // When we see TARGET_LOCAL/TARGET_CAPTURED without an immediately
        // following ASSIGN/MUT_*, we record the target and continue.
        // When we later see MUT_ADD/MUT_SUB, we use the recorded target.
        enum { TGT_NONE, TGT_LOCAL, TGT_CAPTURED, TGT_MEMBER, TGT_SELF_MEMBER, TGT_SUBSCRIPT } tgt_kind;
        int tgt_index;  // local index, capture index, or member id
        int tgt_obj_sp; // for TGT_MEMBER: sp slot where obj was (before pop)

        int label_count;

        // Set after THROW/RETURN --- code is unreachable until next label
        bool dead;

        // JIT trampoline: track call sites for resume dispatch
        int call_site_count;
        int resume_labels[MAX_BC_OPS]; // DynASM labels for resume points
} JitCtx;

// Operand stack offset: address of ops[i] relative to BC_OPS
#define OP_OFF(i) ((i) * VALUE_SIZE)

// Allocate a new DynASM PC label, growing the pclabel array if needed
static int
bc_next_label(JitCtx *ctx)
{
        if (ctx->next_label >= ctx->label_capacity) {
                ctx->label_capacity *= 2;
                dasm_growpc(&ctx->asm, ctx->label_capacity);
        }
        return ctx->next_label++;
}

// Get a DynASM label for a bytecode offset, creating one if needed
static int
bc_label_for(JitCtx *ctx, int offset)
{
        for (int i = 0; i < ctx->label_count; ++i) {
                if (ctx->labels[i].offset == offset) {
                        return ctx->labels[i].label;
                }
        }
        if (ctx->label_count >= MAX_BC_LABELS) {
                return -1;
        }
        int label = bc_next_label(ctx);
        ctx->labels[ctx->label_count].offset = offset;
        ctx->labels[ctx->label_count].label = label;
        ctx->labels[ctx->label_count].sp = -1; // unknown until emission
        ctx->labels[ctx->label_count].save_sp_top = -2; // not set
        ctx->label_count++;
        return label;
}

// Look up a label for a bytecode offset (returns -1 if not found)
static int
bc_find_label(JitCtx *ctx, int offset)
{
        for (int i = 0; i < ctx->label_count; ++i) {
                if (ctx->labels[i].offset == offset) {
                        return ctx->labels[i].label;
                }
        }
        return -1;
}

// Record the expected sp and save_sp state at a jump target
static void
bc_set_label_sp(JitCtx *ctx, int offset, int sp)
{
        // Don't set label sp from unreachable code (after THROW/RETURN)
        if (ctx->dead) return;

        for (int i = 0; i < ctx->label_count; ++i) {
                if (ctx->labels[i].offset == offset) {
                        if (ctx->labels[i].sp == -1) {
                                ctx->labels[i].sp = sp;
                        }
                        if (ctx->labels[i].save_sp_top == -2) {
                                ctx->labels[i].save_sp_top = ctx->save_sp_top;
                                memcpy(ctx->labels[i].save_sp_stack, ctx->save_sp_stack,
                                       (ctx->save_sp_top + 1) * sizeof(int));
                        }
                        return;
                }
        }
}

// Get the expected sp at a label (or -1 if unknown)
static int
bc_get_label_sp(JitCtx *ctx, int offset)
{
        for (int i = 0; i < ctx->label_count; ++i) {
                if (ctx->labels[i].offset == offset) {
                        return ctx->labels[i].sp;
                }
        }
        return -1;
}

inline static void
idbg(JitCtx *ctx, char const *op)
{
        jit_emit_mov(&ctx->asm, BC_A0, BC_TY);
        jit_emit_load_imm(&ctx->asm, BC_A1, ctx->sp);
        jit_emit_load_imm(&ctx->asm, BC_A2, ((iptr)op));
        jit_emit_load_imm(&ctx->asm, BC_CALL, (iptr)jit_rt_idbg);
        jit_emit_call_reg(&ctx->asm, BC_CALL);
}

inline static void
itrc(JitCtx *ctx, char *ip, char const *op)
{
        Expr const *expr = compiler_find_expr(ctx->ty, ip);
        char const *mod;
        int line;
        int col;
        if (expr != NULL) {
                mod = expr->mod->name;
                line = expr->start.line + 1;
                col = expr->start.col + 1;
        } else {
                mod = "??";
                line = 0;
                col = 0;
        }
        char *msg = xfmt(
                "[%14.14s:%d:%d] [%3d] %s",
                mod,
                line,
                col,
                ctx->sp,
                op
        );
        jit_emit_mov(&ctx->asm, BC_A0, BC_TY);
        jit_emit_load_imm(&ctx->asm, BC_A1, ctx->sp);
        jit_emit_load_imm(&ctx->asm, BC_A2, ((iptr)msg));
        jit_emit_load_imm(&ctx->asm, BC_CALL, (iptr)jit_rt_itrc);
        jit_emit_call_reg(&ctx->asm, BC_CALL);
}

// ============================================================================
// ============================================================================
// Bytecode pre-scan: discover jump targets and check supportedness
// ============================================================================

static bool
bc_prescan(JitCtx *ctx, char const *code, int code_size)
{
        Ty *ty = ctx->ty;
        (void)ty;

        char const *ip = code;
        char const *end = code + code_size;

#define BC_READ(var)  do { __builtin_memcpy(&var, ip, sizeof var); ip += sizeof var; } while (0)
#define BC_SKIP(type) (ip += sizeof(type))
#define BC_SKIPSTR()  (ip += strlen(ip) + 1)

        while (ip < end) {
                char const *instr_start = ip;
                int instr_off = (int)(ip - code);
                (void)instr_start;
                (void)instr_off;

                u8 op = (u8)*ip++;
                int n;
                imax k;
                double x;
                bool b;
                int nkw;
                int i, j, tag;
                uptr s;

#if JIT_SCAN_LOG
                LOGX(
                        "[jit] [%12.12s] [%16.16s] scan[%4jd] %s",
                        expr_of(ctx->func)->mod->name,
                        name_of(ctx->func),
                        ip - code - 1, GetInstructionName(op)
                );
#endif

                switch (op) {
                case INSTR_NOP:
                case INSTR_DUP:
                case INSTR_POP:
                case INSTR_POP2:
                case INSTR_SWAP:
                case INSTR_ADD:
                case INSTR_SUB:
                case INSTR_MUL:
                case INSTR_DIV:
                case INSTR_MOD:
                case INSTR_NEG:
                case INSTR_NOT:
                case INSTR_EQ:
                case INSTR_NEQ:
                case INSTR_LT:
                case INSTR_GT:
                case INSTR_LEQ:
                case INSTR_GEQ:
                case INSTR_CMP:
                case INSTR_BIT_AND:
                case INSTR_BIT_OR:
                case INSTR_BIT_XOR:
                case INSTR_SHL:
                case INSTR_SHR:
                case INSTR_CHECK_MATCH:
                case INSTR_RETURN:
                case INSTR_RETURN_PRESERVE_CTX:
                case INSTR_TRUE:
                case INSTR_FALSE:
                case INSTR_NIL:
                case INSTR_ASSIGN:
                case INSTR_MAYBE_ASSIGN:
                case INSTR_SUBSCRIPT:
                case INSTR_TARGET_SUBSCRIPT:
                case INSTR_QUESTION:
                case INSTR_INC:
                case INSTR_DEC:
                case INSTR_COUNT:
                case INSTR_GET_TAG:
                case INSTR_CLASS_OF:
                case INSTR_MUT_ADD:
                case INSTR_MUT_SUB:
                case INSTR_MUT_MUL:
                case INSTR_MUT_DIV:
                case INSTR_MUT_MOD:
                case INSTR_MUT_OR:
                case INSTR_MUT_AND:
                case INSTR_MUT_XOR:
                case INSTR_MUT_SHL:
                case INSTR_MUT_SHR:
                case INSTR_CHECK_INIT:
                case INSTR_NONE_IF_NIL:
                case INSTR_THROW_IF_NIL:
                case INSTR_THROW:
                case INSTR_NONE:
                case INSTR_SENTINEL:
                case INSTR_RETURN_IF_NOT_NONE:
                case INSTR_TO_STRING:
                case INSTR_SLICE:
                        break;

                case INSTR_LOAD_LOCAL:
                case INSTR_LOAD_REF:
                case INSTR_LOAD_CAPTURED:
                        BC_SKIP(i32);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        break;

                case INSTR_ASSIGN_LOCAL:
                case INSTR_TARGET_LOCAL:
                case INSTR_TARGET_REF:
                        BC_SKIP(i32);
                        break;

                case INSTR_TARGET_CAPTURED:
                        BC_SKIP(i32);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        break;

                case INSTR_INT8:
                        ip += 1;
                        break;

                case INSTR_INTEGER:
                        BC_SKIP(imax);
                        break;

                case INSTR_REAL:
                        BC_SKIP(double);
                        break;

                case INSTR_STRING:
                        BC_SKIP(i32);
                        break;

                case INSTR_OPERATOR:
                        BC_SKIP(i32);
                        BC_SKIP(i32);
                        break;

                case INSTR_MEMBER_ACCESS:
                case INSTR_SELF_MEMBER_ACCESS:
                        BC_SKIP(i32);
                        break;

                case INSTR_TARGET_MEMBER:
                case INSTR_TARGET_SELF_MEMBER:
                        BC_SKIP(i32);
                        break;

                case INSTR_JUMP: {
                        int off;
                        BC_READ(off);
                        int target = (int)(ip - code) + off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_JUMP_IF:
                case INSTR_JUMP_IF_NOT:
                case INSTR_JUMP_IF_NIL:
                case INSTR_JUMP_IF_NONE:
                case INSTR_JUMP_AND:
                case INSTR_JUMP_OR: {
                        int off;
                        BC_READ(off);
                        int target = (int)(ip - code) + off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_JUMP_WTF: {
                        int off;
                        BC_READ(off);
                        int target = (int)(ip - code) + off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_JEQ:
                case INSTR_JNE:
                case INSTR_JLT:
                case INSTR_JGT:
                case INSTR_JLE:
                case INSTR_JGE: {
                        int off;
                        BC_READ(off);
                        int target = (int)(ip - code) + off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_CALL:
                        BC_SKIP(i32);  // n (argc)
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;

                case INSTR_CALL_METHOD:
                case INSTR_CALL_SELF_METHOD:
                        BC_SKIP(i32);  // n (argc)
                        BC_SKIP(i32);  // z (member_id)
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;

                case INSTR_LOAD_THREAD_LOCAL:
                        BC_SKIP(i32);
                        break;

                case INSTR_LOAD_GLOBAL:
                        BC_SKIP(i32);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        break;

                case INSTR_ASSIGN_GLOBAL:
                case INSTR_TARGET_GLOBAL:
                        BC_SKIP(i32);
                        break;

                case INSTR_CALL_GLOBAL:
                        BC_SKIP(i32);  // global idx
                        BC_SKIP(i32);  // n (argc)
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;

                case INSTR_VALUE:
                case INSTR_TYPE:
                case INSTR_REGEX:
                        BC_SKIP(uptr);
                        break;

                case INSTR_BAD_CALL:
                        BC_SKIPSTR();
                        BC_SKIPSTR();
                        break;

                case INSTR_BAD_MATCH:
                case INSTR_BAD_DISPATCH:
                case INSTR_BAD_ASSIGN:
                        // BAD_ASSIGN has a string; BAD_MATCH/BAD_DISPATCH have none
                        if (op == INSTR_BAD_ASSIGN) BC_SKIPSTR();
                        break;

                case INSTR_SAVE_STACK_POS:
                case INSTR_POP_STACK_POS:
                case INSTR_POP_STACK_POS_POP:
                case INSTR_RESTORE_STACK_POS:
                        break;

                case INSTR_ARRAY:
                case INSTR_ARRAY0:
                        break;

                case INSTR_ARRAY_COMPR:
                        BC_SKIP(i32);
                        break;

                case INSTR_TUPLE:
                        BC_READ(n);
                        BC_READ(s);
                        break;

                case INSTR_DUP2_SWAP:
                        break;

                case INSTR_ENSURE_LEN_TUPLE: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // expected count
                        break;
                }

                case INSTR_JUMP_IF_TYPE: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // type value
                        break;
                }

                case INSTR_TRY_ASSIGN_NON_NIL: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_TRY_TAG_POP: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // tag
                        break;
                }

                case INSTR_ASSIGN_SUBSCRIPT:
                        break;

                case INSTR_HALT:
                        break;

                case INSTR_TAG:
                case INSTR_CLASS:
                        BC_SKIP(i32);
                        break;

                case INSTR_CONCAT_STRINGS:
                        BC_SKIP(i32);
                        break;

                case INSTR_RANGE:
                case INSTR_INCRANGE:
                        break;

                case INSTR_UNARY_OP:
                case INSTR_BINARY_OP:
                        BC_SKIP(i32);
                        break;

                case INSTR_MATCH_TAG: {
                        ip += 1; // wrapped byte
                        i32 num_entries;
                        BC_READ(num_entries);
                        i32 fail_off;
                        BC_READ(fail_off);
                        int fail_target = (int)(ip - code) + fail_off;
                        if (bc_label_for(ctx, fail_target) < 0) return false;
                        for (i32 q = 0; q < num_entries; ++q) {
                                BC_SKIP(i32); // tag_id
                                i32 jmp_off;
                                BC_READ(jmp_off);
                                int jmp_target = (int)(ip - code) + jmp_off;
                                if (bc_label_for(ctx, jmp_target) < 0) return false;
                        }
                        break;
                }

                case INSTR_RENDER_TEMPLATE:
                        // FIXME: need to emit #holes so JIT knows how to adjust sp
                        return false;

                case INSTR_CAPTURE:
                        BC_SKIP(i32); // local_idx
                        BC_SKIP(i32); // env_idx
                        break;

                case INSTR_BIND_INSTANCE:
                        return false;
                        BC_SKIP(i32);
                        BC_SKIP(i32);
                        break;

                case INSTR_PUSH_TUPLE_ELEM:
                        BC_SKIP(i32);
                        break;

                case INSTR_INDEX_TUPLE: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // idx
                        break;
                }

                case INSTR_TRY_TUPLE_MEMBER: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(u8); // required
                        BC_SKIP(i32); // name_id
                        break;
                }

                case INSTR_PUSH_INDEX:
                        BC_SKIP(i32);
                        break;

                case INSTR_JII: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // class_id
                        break;
                }

                case INSTR_ENSURE_EQUALS_VAR: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_TRY_INDEX: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // idx
                        BC_SKIP(u8); // required
                        break;
                }

                case INSTR_TRY_STEAL_TAG: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_JNI: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // class_id
                        break;
                }

                case INSTR_ENSURE_LEN: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // expected_length
                        break;
                }

                case INSTR_LOOP_ITER:
                case INSTR_CLEAR_RC:
                case INSTR_DICT:
                case INSTR_DEFAULT_DICT:
                        break;

                case INSTR_LOOP_CHECK: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // var_count
                        break;
                }

                case INSTR_CALL_STATIC_METHOD:
                        BC_SKIP(i32);  // class_id
                        BC_SKIP(i32);  // argc
                        BC_SKIP(i32);  // method_id
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;

                case INSTR_FUNCTION: {
                        i32 bound_caps;
                        BC_READ(bound_caps);
                        ip = ALIGNED_FOR(i64, ip);
                        i32 const *fn_info = (i32 const *)ip;
                        int hs   = fn_info[FUN_INFO_HEADER_SIZE];
                        int size = fn_info[FUN_INFO_CODE_SIZE];
                        int nEnv = fn_info[FUN_INFO_CAPTURES];
                        int ncaps = (bound_caps > 0) ? nEnv - bound_caps : nEnv;
                        char const *after = ip + hs + size;
                        for (int q = 0; q < ncaps; ++q) {
                                after += sizeof (bool);
                                after += sizeof (int);
                        }
                        if (hs < 0 || size < 0 || nEnv < 0 || ncaps < 0 || after > end) {
                                return false;
                        }
                        ip = after;
                        break;
                }

                // Unsupported --- bail out
                default:
#if JIT_SCAN_LOG
                        LOGX("JIT: prescan bail on %s at offset %d",
                            GetInstructionName(op), instr_off);
#endif
                        return false;
                }
        }

#undef BC_READ
#undef BC_SKIP
#undef BC_SKIPSTR

        return true;
}

// ============================================================================
// Runtime helpers for bytecode JIT (called from native code)
// ============================================================================

static void
jit_rt_call(Ty *ty, Value *result, Value *fn, int argc)
{
        Value _fn = *fn;
        ptrdiff_t idx = (result - vv(ty->stack));
        vN(ty->stack) = idx + argc;
        DoCall(ty, &_fn, argc, 0, false, true);
}

// Trampoline-aware call helper.
// Returns 0 if the call was handled synchronously (non-JIT or interpreted).
// Returns 1 if the callee is JIT-compiled and the trampoline should dispatch it.
static int
jit_rt_call_trampoline(Ty *ty, Value *result, Value *fn, int argc)
{
        Value _fn = *fn;
        ptrdiff_t idx = (result - vv(ty->stack));
        vN(ty->stack) = idx + argc;

        // Only attempt trampoline for simple function types
        if (_fn.type != VALUE_FUNCTION && _fn.type != VALUE_BOUND_FUNCTION) {
                DoCall(ty, &_fn, argc, 0, false, true);
                return 0;
        }

        // Check if callee is JIT-compiled
        JitFn *jit = try_jit(ty, &_fn);
        if (jit == NULL) {
                // Not JIT-compiled, run synchronously
                DoCall(ty, &_fn, argc, 0, false, true);
                return 0;
        }

        // Callee is JIT-compiled: set up its frame and signal the trampoline
        vm_xcall(ty, &_fn, NULL, argc, NULL);

        ty->jit._fn = jit;
        ty->jit._env = _fn.env;

        return 1;
}
// Fast frame setup for simple functions (no rest args, no kwargs).
// Replaces the expensive xcall() path for known-simple functions.
static inline void
jit_fast_frame(Ty *ty, Value const *fn, Value const *self, int argc)
{
        int bound = fn->info[FUN_INFO_BOUND];
        int fp = vN(ty->stack) - argc;

        // Ensure stack capacity
        int needed = fp + bound;
        if (UNLIKELY((usize)needed > vC(ty->stack))) {
                xvR(ty->stack, needed + 256);
        }

        // NIL-fill locals beyond args
        Value *base = vv(ty->stack) + fp;
        for (int i = argc; i < bound; i++) {
                base[i] = NIL;
        }
        vN(ty->stack) = needed;

        // Set self for methods
        if (self != NULL) {
                int np = fn->info[FUN_INFO_PARAM_COUNT];
                base[np] = *self;
        }

        // Push frame and call return address
        xvP(ty->st.frames, ((Frame){ .fp = fp, .f = *fn, .ip = NULL }));
        xvP(ty->st.calls, (char *)NULL);
}

// Run a JIT function through an inline trampoline loop.
// Handles nested JIT-to-JIT calls without returning to the outer trampoline.
static inline void
jit_run_trampoline(Ty *ty, JitFn *jit, Value **env, int nenv)
{
        int base_depth = ty->jit.depth;
        Value result = {0};
        Value cv = {0};

        ty->jit.cont[ty->jit.depth++] = (JitCont) {
                .fn   = jit,
                .env  = env,
                .ret  = &result,
                .idx  = 0,
        };

        while (ty->jit.depth > base_depth) {
                JitCont *top = &ty->jit.cont[ty->jit.depth - 1];
                usize cfp = vvL(ty->st.frames)->fp;
                Value *args = vv(ty->stack) + cfp;

                if (UNLIKELY(vN(ty->stack) + 256 > vC(ty->stack))) {
                        xvR(ty->stack, vN(ty->stack) + 256);
                        args = vv(ty->stack) + cfp;
                }

                ty->jit.idx    = top->idx;
                ty->jit.status = JIT_RETURN;

                (*(JitFn *)top->fn)(ty, top->ret, args, top->env);

                if (ty->jit.status == JIT_CALL) {
                        top->idx = ty->jit._idx;
                        ty->jit.cont[ty->jit.depth++] = (JitCont) {
                                .fn   = ty->jit._fn,
                                .env  = ty->jit._env,
                                .ret  = &cv,
                                .idx  = 0,
                        };
                } else if (--ty->jit.depth > base_depth) {
                        cfp = vvL(ty->st.frames)->fp;
                        vN(ty->stack) = cfp + 1;
                        *v_(ty->stack, cfp) = cv;
                        vXx(ty->st.frames);
                        vXx(ty->st.calls);
                        vm_check_flags(ty);
                }
        }

        // Clean up the initial callee's frame
        usize cfp = vvL(ty->st.frames)->fp;
        vN(ty->stack) = cfp + 1;
        *v_(ty->stack, cfp) = result;
        vXx(ty->st.frames);
        vXx(ty->st.calls);
}

// Fast baked method call with inline trampoline.
// Returns 1 if handled (result on stack), 0 for fallback to slow path.
static int
jit_rt_baked_call(Ty *ty, Value *self, Value *fn, int class_id, int argc)
{
        // Class guard
        if (UNLIKELY(ClassOf(self) != class_id)) {
                return 0;
        }

        // Check if callee is JIT-compiled
        JitFn *jit = try_jit(ty, fn);
        if (UNLIKELY(jit == NULL)) {
                return 0;
        }

        Value _self = *self;

        STAT(call_method_baked);

        // Fast frame setup (no xcall overhead)
        jit_fast_frame(ty, fn, &_self, argc);

        // Run callee via inline trampoline (handles nested JIT calls)
        jit_run_trampoline(ty, jit, fn->env, fn->info[FUN_INFO_CAPTURES]);

        return 1;
}

// Fast global function call with inline trampoline.
// Returns 1 if handled, 0 for fallback.
static int
jit_rt_fast_global_call(Ty *ty, int gi, int argc)
{
        Value *fn = vm_global(ty, gi);

        // Only attempt for simple function types
        if (fn->type != VALUE_FUNCTION && fn->type != VALUE_BOUND_FUNCTION) {
                return 0;
        }

        // Check if callee is JIT-compiled
        JitFn *jit = try_jit(ty, fn);
        if (jit == NULL) {
                return 0;
        }

        // Fast frame setup
        jit_fast_frame(ty, fn, NULL, argc);

        // Run callee via inline trampoline
        jit_run_trampoline(ty, jit, fn->env, fn->info[FUN_INFO_CAPTURES]);

        return 1;
}

static void
jit_rt_call_method(Ty *ty, Value *result, Value *self, int member_id, int argc)
{
        ptrdiff_t idx = (result - vv(ty->stack));
        vN(ty->stack) = idx + argc;
        if (self == NULL) {
                self = vm_get_self(ty);
        }
        xvP(ty->stack, *self);
        CallMethod(ty, member_id, argc, 0, true, true);
}

// Call a method directly with a baked Value* (fast path when class is known at JIT time)
static void
jit_rt_call_method_direct(Ty *ty, Value *result, Value *self, Value *method, int argc)
{
        ptrdiff_t idx = (result - vv(ty->stack));
        vN(ty->stack) = idx + argc;
        Value val = vm_call_method(ty, self, method, argc);
        *v_(ty->stack, idx) = val;
}

// Guarded CALL_SELF_METHOD fast path w/ baked method ptr
// class_and_member packs class_id (high 32) and member_id (low 32)
static void
jit_rt_call_self_method_guarded(Ty *ty, Value *result, Value *self,
                                Value *baked, int64_t class_and_member, int argc)
{
        int class_id  = (int)(class_and_member >> 32);
        int member_id = (int)(class_and_member);

        if (self == NULL) {
                self = vm_get_self(ty);
        }

        if (ClassOf(self) == class_id) {
                STAT(call_method_baked);
                jit_rt_call_method_direct(ty, result, self, baked, argc);
        } else {
                STAT(call_method_slow);
                SLOW_RECORD(ty, jit_stats_call_ip, SLOW_CALL_METHOD, self, NULL);
                jit_rt_call_method(ty, result, self, member_id, argc);
        }
}

// Guarded CALL_METHOD fast path for primitive type builtins
// vtype_and_member packs value_type (high 32) and member_id (low 32)
static void
jit_rt_call_builtin_method(Ty *ty, Value *result, Value *self,
                           BuiltinMethod *func, int64_t vtype_and_member, int argc)
{
        int value_type = (int)(vtype_and_member >> 32);
        int member_id  = (int)(vtype_and_member);

        if (self == NULL) {
                self = vm_get_self(ty);
        }

        Value _self = *self;

        if (LIKELY(self->type == value_type)) {
                STAT(call_method_builtin);
                ptrdiff_t idx = (result - vv(ty->stack));
                vN(ty->stack) = idx + argc;
                gP(&_self);
                Value val = (*func)(ty, &_self, argc, NULL);
                vN(ty->stack) = idx + 1;
                v_L(ty->stack) = val;
                vm_check_flags(ty);
                gX();
        } else {
                STAT(call_method_slow);
                SLOW_RECORD(ty, jit_stats_call_ip, SLOW_CALL_METHOD, &_self, NULL);
                jit_rt_call_method(ty, result, &_self, member_id, argc);
        }
}

// Direct call to a builtin function (global known to be const at JIT compile time)
static void
jit_rt_call_builtin_function(Ty *ty, Value *result, BuiltinFunction *func, int argc)
{
        ptrdiff_t idx = (result - vv(ty->stack));
        vN(ty->stack) = idx + argc;
        Value val = func(ty, argc, NULL);
        vN(ty->stack) = idx + 1;
        v_L(ty->stack) = val;
        vm_check_flags(ty);
}

static void
jit_rt_check_match(Ty *ty, Value *result, Value *value, Value *pattern)
{
        vN(ty->stack) = result - vv(ty->stack) + 2;
        DoCheckMatch(ty, true);
}


static int
jit_rt_compare(Ty *ty, Value *a, Value *b)
{
        return value_compare(ty, a, b);
}

static void
jit_rt_concat_strings(Ty *ty, Value *result, Value *base, int n)
{
        usize total = 0;
        for (int i = 0; i < n; ++i) {
                Value *v = (Value *)((char *)base + i * VALUE_SIZE);
                total += sN(*v);
        }
        char *str = uAo(total, GC_STRING);
        usize k = 0;
        for (int i = 0; i < n; ++i) {
                Value *v = (Value *)((char *)base + i * VALUE_SIZE);
                if (sN(*v) > 0) {
                        memcpy(str + k, ss(*v), sN(*v));
                        k += sN(*v);
                }
        }
        *result = STRING(str, total);
}

// ============================================================================
// Bytecode emission
// ============================================================================

static void
bc_copy_value(JitCtx *ctx, int dst_reg, int dst_off, int src_reg, int src_off)
{
        dasm_State **asm = &ctx->asm;

        // ldp x,x,[base,#imm] requires signed 7-bit scaled offset: range [-512, 504]
        bool src_direct = (src_off >= -512 && src_off + 16 <= 504);
        bool dst_direct = (dst_off >= -512 && dst_off + 16 <= 504);

        int sa = src_reg, so0 = src_off, so1 = src_off + 16;
        int da = dst_reg, do0 = dst_off, do1 = dst_off + 16;

        // Detect register conflicts between fixup targets and direct operands:
        //   src fixup writes BC_S2; conflicts if dst_reg == BC_S2 and dst is direct
        //   dst fixup writes BC_S3; conflicts if src_reg == BC_S3 and src is direct
        // Fix: force the direct side into its scratch reg first to save the base.
        if (src_direct && src_reg == BC_S3 && !dst_direct) {
                jit_emit_add_imm(asm, BC_S2, src_reg, src_off);
                sa = BC_S2; so0 = 0; so1 = 16;
                src_direct = false;
        }
        if (dst_direct && dst_reg == BC_S2 && !src_direct) {
                jit_emit_add_imm(asm, BC_S3, dst_reg, dst_off);
                da = BC_S3; do0 = 0; do1 = 16;
                dst_direct = false;
        }

        // When both need fixup and dst_reg == BC_S2, compute dst first
        // so src fixup doesn't clobber the dst base register.
        if (!src_direct && !dst_direct && sa != BC_S2 && da != BC_S3) {
                if (dst_reg == BC_S2) {
                        jit_emit_add_imm(asm, BC_S3, dst_reg, dst_off);
                        da = BC_S3; do0 = 0; do1 = 16;
                        jit_emit_add_imm(asm, BC_S2, src_reg, src_off);
                        sa = BC_S2; so0 = 0; so1 = 16;
                } else {
                        jit_emit_add_imm(asm, BC_S2, src_reg, src_off);
                        sa = BC_S2; so0 = 0; so1 = 16;
                        jit_emit_add_imm(asm, BC_S3, dst_reg, dst_off);
                        da = BC_S3; do0 = 0; do1 = 16;
                }
        } else {
                if (!src_direct && sa != BC_S2) {
                        jit_emit_add_imm(asm, BC_S2, src_reg, src_off);
                        sa = BC_S2; so0 = 0; so1 = 16;
                }
                if (!dst_direct && da != BC_S3) {
                        jit_emit_add_imm(asm, BC_S3, dst_reg, dst_off);
                        da = BC_S3; do0 = 0; do1 = 16;
                }
        }

        jit_emit_ldp64(asm, BC_S0, BC_S1, sa, so0);
        jit_emit_stp64(asm, BC_S0, BC_S1, da, do0);
        jit_emit_ldp64(asm, BC_S0, BC_S1, sa, so1);
        jit_emit_stp64(asm, BC_S0, BC_S1, da, do1);
}

static void
bc_push_from(JitCtx *ctx, int src_reg, int src_off)
{
        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), src_reg, src_off);
        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
}

static void
bc_pop_to(JitCtx *ctx, int dst_reg, int dst_off)
{
        ctx->sp--;
        bc_copy_value(ctx, dst_reg, dst_off, BC_OPS, OP_OFF(ctx->sp));
}

static void
bc_emit_deref(JitCtx *ctx, int dst, int src, int src_off)
{
        dasm_State **asm = &ctx->asm;

        int lbl_skip = bc_next_label(ctx);

        jit_emit_add_imm(asm, dst, src, src_off);
        jit_emit_ldrb(asm, BC_S0, dst, VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_REF);
        jit_emit_branch_ne(asm, lbl_skip);
        jit_emit_ldr64(asm, dst, dst, VAL_OFF_REF);
        jit_emit_label(asm, lbl_skip);
}

static void
bc_emit_interrupt_check(JitCtx *ctx)
{
        dasm_State **asm = &ctx->asm;

        int lbl_no_irq = bc_next_label(ctx);
        jit_emit_load_imm(asm, BC_S0, (iptr)&JitInterruptFlag);
        jit_emit_ldr32(asm, BC_S0, BC_S0, 0);
        jit_emit_cbz(asm, BC_S0, lbl_no_irq);
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
        jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_handle_interrupt);
        jit_emit_call_reg(asm, BC_CALL);
        jit_emit_label(asm, lbl_no_irq);
}

static void
bc_push_integer(JitCtx *ctx, intmax_t val)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp);

        // Zero the entire 32-byte slot first (type, tags, src, etc.)
        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

        // Set type = VALUE_INTEGER
        jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

        // Set z = val
        jit_emit_load_imm(asm, BC_S0, val);
        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;

        ctx->op_types[ctx->sp - 1] = INT_TYPE;
}

static void
bc_push_bool(JitCtx *ctx, bool val)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp);

        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

        jit_emit_load_imm(asm, BC_S0, VALUE_BOOLEAN);
        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

        jit_emit_load_imm(asm, BC_S0, val ? 1 : 0);
        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;

        ctx->op_types[ctx->sp - 1] = BOOL_TYPE;
}

static void
bc_push_nil(JitCtx *ctx)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp);

        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

        jit_emit_load_imm(asm, BC_S0, VALUE_NIL);
        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;

        ctx->op_types[ctx->sp - 1] = NIL_TYPE;
}

// a = ops[sp-2], b = ops[sp-1], result = ops[sp-2], sp--
static void
bc_emit_binop_helper(JitCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;

        // x0 = ty
        jit_emit_mov(asm, BC_A0, BC_TY);
        // x1 = &ops[sp-2] (result)
        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp - 2));
        // x2 = &ops[sp-2] (a)
        jit_emit_mov(asm, BC_A2, BC_A1);
        // x3 = &ops[sp-1] (b)
        jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp - 1));

        jit_emit_load_imm(asm, BC_CALL, (iptr)helper);
        jit_emit_call_reg(asm, BC_CALL);

        ctx->sp--;
}

static void
bc_emit_unop_helper(JitCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;

        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp - 1));
        jit_emit_mov(asm, BC_A2, BC_A1);

        jit_emit_load_imm(asm, BC_CALL, (iptr)helper);
        jit_emit_call_reg(asm, BC_CALL);
}

static void
bc_emit_arith(JitCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;
        int a_off = OP_OFF(ctx->sp - 2);
        int b_off = OP_OFF(ctx->sp - 1);

        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);

        // Check a->type == VALUE_INTEGER
        jit_emit_ldrb(asm, BC_S0, BC_OPS, a_off + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_ne(asm, lbl_slow);

        // Check b->type == VALUE_INTEGER
        jit_emit_ldrb(asm, BC_S0, BC_OPS, b_off + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_ne(asm, lbl_slow);

        // Fast path: load integers, compute, store result
        jit_emit_ldr64(asm, BC_S0, BC_OPS, a_off + VAL_OFF_Z);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, b_off + VAL_OFF_Z);

        // Guard div/mod against zero divisor (SIGFPE on x64, wrong result on arm64)
        if (helper == (void *)jit_rt_div || helper == (void *)jit_rt_mod) {
                jit_emit_cbz(asm, BC_S1, lbl_slow);
        }

        if (helper == (void *)jit_rt_add) {
                jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_sub) {
                jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_mul) {
                jit_emit_mul(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_div) {
                jit_emit_sdiv(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_mod) {
                jit_emit_mod(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_bit_and) {
                jit_emit_and(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_bit_or) {
                jit_emit_or(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_bit_xor) {
                jit_emit_xor(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_shl) {
                jit_emit_shl(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_shr) {
                jit_emit_shr(asm, BC_S0, BC_S0, BC_S1);
        }

        // Store result z into ops[sp-2]
        jit_emit_str64(asm, BC_S0, BC_OPS, a_off + VAL_OFF_Z);
        // Type is already VALUE_INTEGER
        jit_emit_jump(asm, lbl_done);

        // Slow path
        jit_emit_label(asm, lbl_slow);
        bc_emit_binop_helper(ctx, helper);
        ctx->sp++; // bc_emit_binop_helper decremented sp, but we want to undo it here
                   // since we decrement once below

        jit_emit_label(asm, lbl_done);
        ctx->sp--;
}

static void
bc_write_bool(JitCtx *ctx, int off, int val_reg)
{
        dasm_State **asm = &ctx->asm;
        jit_emit_load_imm(asm, BC_S1, 0);
        jit_emit_stp64(asm, BC_S1, BC_S1, BC_OPS, off);
        jit_emit_stp64(asm, BC_S1, BC_S1, BC_OPS, off + 16);
        jit_emit_load_imm(asm, BC_S1, VALUE_BOOLEAN);
        jit_emit_strb(asm, BC_S1, BC_OPS, off + VAL_OFF_TYPE);
        jit_emit_str64(asm, val_reg, BC_OPS, off + VAL_OFF_Z);
}

static Class *expected_class_of(Ty *ty, Type const *t);

// Emit: type-directed fast paths for comparison ops.
// Uses expected_class_of() to decide which fast path to emit:
//   CLASS_INT    => inline integer comparison
//   CLASS_STRING => call jit_rt_str_eq (EQ/NEQ only)
//   NULL/other   => no typed fast path
// EQ/NEQ always get a cheap nil check before the slow path.
static void
bc_emit_cmp(JitCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;
        int a_off = OP_OFF(ctx->sp - 2);
        int b_off = OP_OFF(ctx->sp - 1);

        bool is_eq_or_ne = (helper == (void *)jit_rt_eq || helper == (void *)jit_rt_ne);
        Class *cls = expected_class_of(ctx->ty, ctx->op_types[ctx->sp - 1]);

        // For non-equality ops with no int fast path, just call the helper
        if (!is_eq_or_ne && (cls == NULL || cls->i != CLASS_INT)) {
                bc_emit_binop_helper(ctx, helper);
                return;
        }

        int lbl_nil_check = bc_next_label(ctx);
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);

        // Load both types
        jit_emit_ldrb(asm, BC_S0, BC_OPS, a_off + VAL_OFF_TYPE); // a.type
        jit_emit_ldrb(asm, BC_S1, BC_OPS, b_off + VAL_OFF_TYPE); // b.type

        if (cls != NULL && cls->i == CLASS_INT) {
                // === Integer fast path ===
                jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                jit_emit_branch_ne(asm, is_eq_or_ne ? lbl_nil_check : lbl_slow);

                jit_emit_cmp_ri(asm, BC_S1, VALUE_INTEGER);
                jit_emit_branch_ne(asm, is_eq_or_ne ? lbl_nil_check : lbl_slow);

                jit_emit_ldr64(asm, BC_S0, BC_OPS, a_off + VAL_OFF_Z);
                jit_emit_ldr64(asm, BC_S1, BC_OPS, b_off + VAL_OFF_Z);

                if (helper == (void *)jit_rt_eq) {
                        jit_emit_cmp_eq(asm, BC_S0, BC_S0, BC_S1);
                } else if (helper == (void *)jit_rt_ne) {
                        jit_emit_cmp_ne(asm, BC_S0, BC_S0, BC_S1);
                } else if (helper == (void *)jit_rt_lt) {
                        jit_emit_cmp_lt(asm, BC_S0, BC_S0, BC_S1);
                } else if (helper == (void *)jit_rt_gt) {
                        jit_emit_cmp_gt(asm, BC_S0, BC_S0, BC_S1);
                } else if (helper == (void *)jit_rt_le) {
                        jit_emit_cmp_le(asm, BC_S0, BC_S0, BC_S1);
                } else if (helper == (void *)jit_rt_ge) {
                        jit_emit_cmp_ge(asm, BC_S0, BC_S0, BC_S1);
                }

                bc_write_bool(ctx, a_off, BC_S0);
                jit_emit_jump(asm, lbl_done);
        } else if (is_eq_or_ne && cls != NULL && cls->i == CLASS_STRING) {
                // === String fast path (EQ/NEQ only) ===
                jit_emit_cmp_ri(asm, BC_S0, VALUE_STRING);
                jit_emit_branch_ne(asm, lbl_nil_check);

                jit_emit_cmp_ri(asm, BC_S1, VALUE_STRING);
                jit_emit_branch_ne(asm, lbl_nil_check);

                // Both strings: call jit_rt_str_eq(a, b)
                jit_emit_add_imm(asm, BC_A0, BC_OPS, a_off);
                jit_emit_add_imm(asm, BC_A1, BC_OPS, b_off);
                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_str_eq);
                jit_emit_call_reg(asm, BC_CALL);
                jit_emit_mov(asm, BC_S0, BC_RET); // return value

                if (helper == (void *)jit_rt_ne) {
                        jit_emit_load_imm(asm, BC_S1, 1);
                        jit_emit_xor(asm, BC_S0, BC_S0, BC_S1);
                }

                bc_write_bool(ctx, a_off, BC_S0);
                jit_emit_jump(asm, lbl_done);
        }

        // === Nil fast path (EQ/NEQ only) ===
        jit_emit_label(asm, lbl_nil_check);
        if (is_eq_or_ne) {
                // BC_S0 = a.type, BC_S1 = b.type (still valid from initial load)
                jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                int lbl_a_nil = bc_next_label(ctx);
                jit_emit_branch_eq(asm, lbl_a_nil);
                jit_emit_cmp_ri(asm, BC_S1, VALUE_NIL);
                jit_emit_branch_ne(asm, lbl_slow);

                // b is nil, a is not nil
                jit_emit_load_imm(asm, BC_S0, (helper == (void *)jit_rt_ne) ? 1 : 0);
                bc_write_bool(ctx, a_off, BC_S0);
                jit_emit_jump(asm, lbl_done);

                // a is nil
                jit_emit_label(asm, lbl_a_nil);
                if (helper == (void *)jit_rt_eq) {
                        jit_emit_cmp_eq(asm, BC_S0, BC_S1, BC_S0);
                } else {
                        jit_emit_cmp_ne(asm, BC_S0, BC_S1, BC_S0);
                }
                bc_write_bool(ctx, a_off, BC_S0);
                jit_emit_jump(asm, lbl_done);
        } else {
                jit_emit_jump(asm, lbl_slow);
        }

        // Slow path: call helper
        jit_emit_label(asm, lbl_slow);
        bc_emit_binop_helper(ctx, helper);
        jit_emit_label(asm, lbl_done);
}

static void
bc_emit_truthy(JitCtx *ctx)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp - 1);

        int lbl_nil  = bc_next_label(ctx);
        int lbl_bool = bc_next_label(ctx);
        int lbl_int  = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);

        // Load type byte
        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

        // Fast nil
        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
        jit_emit_branch_eq(asm, lbl_nil);

        // Fast Bool
        jit_emit_cmp_ri(asm, BC_S0, VALUE_BOOLEAN);
        jit_emit_branch_eq(asm, lbl_bool);

        // Fast Int
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_eq(asm, lbl_int);

        // Everything else: call helper
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_truthy);
        jit_emit_call_reg(asm, BC_CALL);
        jit_emit_mov(asm, BC_S0, BC_RET);
        jit_emit_jump(asm, lbl_done);

        // Fast nil => false
        jit_emit_label(asm, lbl_nil);
        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_jump(asm, lbl_done);

        // Fast Bool => identity
        jit_emit_label(asm, lbl_bool);
        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
        jit_emit_jump(asm, lbl_done);

        // Fast Int => (z != 0)
        jit_emit_label(asm, lbl_int);
        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
        jit_emit_load_imm(asm, BC_S1, 0);
        jit_emit_cmp_ne(asm, BC_S0, BC_S0, BC_S1);

        jit_emit_label(asm, lbl_done);
}

static bool
bc_emit_self_member_read_fast(JitCtx *ctx, int member_id, char const *bc_ip)
{
        (void)bc_ip;
        if (ctx->self_class == NULL) return false;

        Ty *ty = ctx->ty;
        Class *cls = ctx->self_class;

        if (member_id >= (int)vN(cls->offsets_r)) return false;

        u16 off = v__(cls->offsets_r, member_id);
        if (off == OFF_NOT_FOUND) return false;

        u16 kind = off >> OFF_SHIFT;
        if (kind != OFF_FIELD) return false;

        u16 slot_idx = off & OFF_MASK;
        int class_id = ctx->self_class_id;
        int slot_byte_off = OBJ_OFF_SLOTS + slot_idx * VALUE_SIZE;

        // Check offset fits in ARM64 ldp range (need slot_byte_off + 16 <= 504)
        if (slot_byte_off + 16 > 504) return false;

        dasm_State **asm = &ctx->asm;
        int self_val_off = ctx->param_count * VALUE_SIZE;
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);

        // Allocate the output slot
        int out_off = OP_OFF(ctx->sp);
        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;

        bc_emit_deref(ctx, BC_S3, BC_LOC, self_val_off);

        // Skip class ID check for private fields since they can't be overridden
        if (strchr(M_NAME(member_id), '$') == NULL) {
                // Check self.class == expected_class_id
                jit_emit_ldr32(asm, BC_S0, BC_S3, VAL_OFF_CLASS);
                jit_emit_cmp_ri(asm, BC_S0, class_id);
                jit_emit_branch_ne(asm, lbl_slow);
        }

        // Check self.object->dynamic == NULL (layout changed at runtime)
        jit_emit_ldr64(asm, BC_S0, BC_S3, VAL_OFF_OBJECT);
        jit_emit_ldr64(asm, BC_S0, BC_S0, OBJ_OFF_DYN);
        jit_emit_cmp_ri(asm, BC_S0, 0);
        jit_emit_branch_ne(asm, lbl_slow);

        // Fast path: load self.object => BC_S2, then copy slot to ops
        EMIT_STAT(jit_rt_stat_self_member_read_fast);
        jit_emit_ldr64(asm, BC_S2, BC_S3, VAL_OFF_OBJECT);
        bc_copy_value(ctx, BC_OPS, out_off, BC_S2, slot_byte_off);
        jit_emit_jump(asm, lbl_done);

        // Slow path: copy self to ops, call jit_rt_member
        jit_emit_label(asm, lbl_slow);
        EMIT_SLOW1(bc_ip, SLOW_SELF_MEMBER_READ, BC_LOC, self_val_off);
        bc_copy_value(ctx, BC_OPS, out_off, BC_LOC, self_val_off);
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, out_off);
        jit_emit_load_imm(asm, BC_A2, 0);
        jit_emit_load_imm(asm, BC_A3, member_id);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
        jit_emit_call_reg(asm, BC_CALL);

        jit_emit_label(asm, lbl_done);
        return true;
}

// Type-guided fast path: TARGET_SELF_MEMBER + ASSIGN with known class
static bool
bc_emit_self_member_write_fast(JitCtx *ctx, int member_id, char const *bc_ip)
{
        (void)bc_ip;
        if (ctx->self_class == NULL) return false;

        Ty *ty = ctx->ty;
        Class *cls = ctx->self_class;

        if (member_id >= (int)vN(cls->offsets_w)) return false;

        u16 off = v__(cls->offsets_w, member_id);
        if (off == OFF_NOT_FOUND) return false;

        u16 kind = off >> OFF_SHIFT;
        if (kind != OFF_FIELD) return false;

        u16 slot_idx = off & OFF_MASK;
        int class_id = ctx->self_class_id;
        int slot_byte_off = OBJ_OFF_SLOTS + slot_idx * VALUE_SIZE;

        if (slot_byte_off + 16 > 504) return false;

        dasm_State **asm = &ctx->asm;
        int self_val_off = ctx->param_count * VALUE_SIZE;
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);
        int val_off = OP_OFF(ctx->sp - 1);

        bc_emit_deref(ctx, BC_S3, BC_LOC, self_val_off);

        if (strchr(M_NAME(member_id), '$') == NULL) {
                // Check self.class == expected_class_id
                jit_emit_ldr32(asm, BC_S0, BC_S3, VAL_OFF_CLASS);
                jit_emit_cmp_ri(asm, BC_S0, class_id);
                jit_emit_branch_ne(asm, lbl_slow);
        }

        // Check self.object->dynamic == NULL (layout changed at runtime)
        jit_emit_ldr64(asm, BC_S0, BC_S3, VAL_OFF_OBJECT);
        jit_emit_ldr64(asm, BC_S0, BC_S0, OBJ_OFF_DYN);
        jit_emit_cmp_ri(asm, BC_S0, 0);
        jit_emit_branch_ne(asm, lbl_slow);

        // Fast path: load self.object => BC_S2, copy val to slot
        EMIT_STAT(jit_rt_stat_self_member_write_fast);
        jit_emit_ldr64(asm, BC_S2, BC_S3, VAL_OFF_OBJECT);
        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, val_off);
        jit_emit_stp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off);
        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, val_off + 16);
        jit_emit_stp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off + 16);
        jit_emit_jump(asm, lbl_done);

        // Slow path: call jit_rt_member_set
        jit_emit_label(asm, lbl_slow);
        EMIT_SLOW1(bc_ip, SLOW_SELF_MEMBER_WRITE, BC_LOC, self_val_off);
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_load_imm(asm, BC_A1, 0);
        jit_emit_load_imm(asm, BC_A2, member_id);
        jit_emit_add_imm(asm, BC_A3, BC_OPS, val_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member_set);
        jit_emit_call_reg(asm, BC_CALL);

        jit_emit_label(asm, lbl_done);
        // val stays on stack (ASSIGN peeks, doesn't pop)
        return true;
}

static Class *
expected_class_of(Ty *ty, Type const *t)
{
        Class *c = type_guess_class_of(ty, t);

        if (c != NULL && c->is_trait) {
                c = NULL;
        }

        return c;
}

static Type *
find_type_hint(TypeHintVector const *hints, iptr off)
{
        isize lo = 0;
        isize hi = vN(*hints) - 1;

        while (lo <= hi) {
                isize m = (lo + hi) / 2;
                TypeHint *hint = v_(*hints, m);
                if (hint->pc == off) {
                        return hint->type;
                } else if (hint->pc < off) {
                        lo = m + 1;
                } else {
                        hi = m - 1;
                }
        }

        return NULL;
}

static Value *
bc_resolve_method(JitCtx *ctx, Class *cls, int member_id)
{
        Ty *ty = ctx->ty;

        if (member_id >= (int)vN(cls->offsets_r)) {
                return NULL;
        }

        u16 off = v__(cls->offsets_r, member_id);
        if (off == OFF_NOT_FOUND) {
                return NULL;
        }

        u16 kind = (off >> OFF_SHIFT);
        if (kind != OFF_METHOD) {
                return NULL;
        }

        u16 method_idx = (off & OFF_MASK);

        Value *method = v_(cls->methods.values, method_idx);

        if (method->type != VALUE_FUNCTION) {
                return NULL;
        }

        return v_(cls->methods.values, method_idx);
}

static BuiltinMethod *
bc_resolve_builtin_method(Class *cls, int member_id, int *value_type)
{
        BuiltinMethod *func = NULL;
        int vtype = -1;

        switch (cls->i) {
        case CLASS_STRING:
                func = get_string_method_i(member_id);
                vtype = VALUE_STRING;
                break;

        case CLASS_ARRAY:
                func = get_array_method_i(member_id);
                vtype = VALUE_ARRAY;
                break;

        case CLASS_DICT:
                func = get_dict_method_i(member_id);
                vtype = VALUE_DICT;
                break;

        case CLASS_BLOB:
                func = get_blob_method_i(member_id);
                vtype = VALUE_BLOB;
                break;

        case CLASS_QUEUE:
                func = get_queue_method_i(member_id);
                vtype = VALUE_QUEUE;
                break;

        case CLASS_SHARED_QUEUE:
                func = get_shared_queue_method_i(member_id);
                vtype = VALUE_SHARED_QUEUE;
                break;

        default:
                break;
        }

        if (func != NULL && value_type != NULL) {
                *value_type = vtype;
        }

        return func;
}

#if JIT_RT_DEBUG
#define CASE(name)                       \
        case INSTR_##name:               \
                ctx->last_op = #name;    \
                idbg(ctx, ">> " #name);
#elif JIT_RT_TRACE
#define CASE(name)                       \
        case INSTR_##name:               \
                ctx->last_op = #name;    \
                itrc(ctx, ip - 1, #name);
#else
#define CASE(name)                \
        case INSTR_##name:        \
                ctx->last_op = #name;
#endif

#if JIT_SCAN_LOG
#define BAIL(fmt, ...) do {                                                     \
        LOGX("JIT[scan]: cannot emit %s at offset %d: " fmt,                    \
                ctx->last_op, (int)(ip - code - 1) __VA_OPT__(,) __VA_ARGS__);  \
        return false;                                                           \
} while (0)
#else
#define BAIL(...) do { \
        return false;  \
} while (0)
#endif

#define XBAIL(fmt, ...) do {                                                    \
        LOGX("JIT[scan]: cannot emit %s at offset %d: " fmt,                    \
                ctx->last_op, (int)(ip - code - 1) __VA_OPT__(,) __VA_ARGS__);  \
        abort();                                                                \
} while (0)

#define SAVE_STACK_POS()
#define POP_STACK_POS(n)
#define DROP_STACK_POS()
#define RESTORE_STACK_POS()

#if 0
#define EMIT_SP_SYNC() jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);
#else
#define EMIT_SP_SYNC()
#endif

#define IRQ_CHECK(n) do {                      \
        if ((n) < 0) {                         \
                bc_emit_interrupt_check(ctx);  \
        }                                      \
} while (0)

static void
bc_emit_call_method(JitCtx *ctx, char const *op_ip, int z, int n, int nkw)
{
        dasm_State **asm = &ctx->asm;

        DBG("CALL_METHOD[%s]: n=%d, z=%d, nkw=%d", M_NAME(z), n, z, nkw);

        EMIT_SET_CALL_IP(op_ip);

        // VM stack layout: [... arg0 arg1 ... argN-1 self]
        // self is at ops[sp-1] (top), args at ops[sp-1-n..sp-2]

        // Try to resolve method at compile time using receiver type info
        Class *recv_cls = expected_class_of(ctx->ty, ctx->op_types[ctx->sp - 1]);

        // Try builtin type fast path (String, Array, Dict, Blob)
        int builtin_vtype = -1;
        BuiltinMethod *builtin_method = (recv_cls != NULL)
                ? bc_resolve_builtin_method(recv_cls, z, &builtin_vtype)
                : NULL;

        // Try object method baking (for user-defined classes)
        Value *baked_method = (recv_cls != NULL)
                ? bc_resolve_method(ctx, recv_cls, z)
                : NULL;

        // self is at ops[sp-1], result goes where args+self were
        int self_off = OP_OFF(ctx->sp - 1);
        int result_off = OP_OFF(ctx->sp - 1 - n); // replaces args+self with result

        if (builtin_method != NULL) {
                // Direct builtin call with type guard
                jit_emit_mov(asm, BC_A0, BC_TY);
                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);
                jit_emit_load_imm(asm, BC_A3, (iptr)builtin_method);
                jit_emit_load_imm(asm, BC_A4, PACK32(builtin_vtype, z));
                jit_emit_load_imm(asm, BC_A5, n);
                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_builtin_method);
                jit_emit_call_reg(asm, BC_CALL);
                DBG("CALL_METHOD (builtin fast path for %s)", M_NAME(z));
        } else if (baked_method != NULL) {
                // Check if the baked method is simple enough for fast trampoline
                bool can_tramp = (rest_idx_of(baked_method) == -1)
                              && (kwargs_idx_of(baked_method) == -1);
                if (can_tramp) {
                        // Fast trampoline path: skip xcall entirely
                        // Sync to sp-1 (exclude self): callee's fp = vN - argc
                        // must land on arg0, which is at op position sp-1-n
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, self_off);
                        jit_emit_load_imm(asm, BC_A2, (iptr)baked_method);
                        jit_emit_load_imm(asm, BC_A3, recv_cls->i);
                        jit_emit_load_imm(asm, BC_A4, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_baked_call);
                        jit_emit_call_reg(asm, BC_CALL);

                        int lbl_cm_done = bc_next_label(ctx);

                        // If return 1: handled (result on stack), skip slow path
                        jit_emit_cbnz(asm, BC_RET, lbl_cm_done);

                        // Slow fallback: guard failed or not JIT'd
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);
                        jit_emit_load_imm(asm, BC_A3, (iptr)baked_method);
                        jit_emit_load_imm(asm, BC_A4, PACK32(recv_cls->i, z));
                        jit_emit_load_imm(asm, BC_A5, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_self_method_guarded);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_cm_done);
                        DBG("CALL_METHOD (baked trampoline for %s)", M_NAME(z));
                } else {
                        // Guarded fast path for user-defined classes (no trampoline)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);
                        jit_emit_load_imm(asm, BC_A3, (iptr)baked_method);
                        jit_emit_load_imm(asm, BC_A4, PACK32(recv_cls->i, z));
                        jit_emit_load_imm(asm, BC_A5, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_self_method_guarded);
                        jit_emit_call_reg(asm, BC_CALL);
                }
        } else {
                jit_emit_mov(asm, BC_A0, BC_TY);
                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);  // result
                jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);    // self
                jit_emit_load_imm(asm, BC_A3, z);
                jit_emit_load_imm(asm, BC_A4, n);
                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_method);
                jit_emit_call_reg(asm, BC_CALL);
                DBG("CALL_METHOD (generic fast path)");
        }

        // Pop self + n args, push result
        ctx->sp -= n; // was n+1 slots (args+self), now 1 slot (result)

        DBG("CALL_METHOD[%s]", M_NAME(z));
}

// Main bytecode emission pass
static bool
bc_emit(JitCtx *ctx, char const *code, int code_size)
{
        Ty *ty = ctx->ty;
        (void)ty;

        dasm_State **asm = &ctx->asm;
        char const *ip = code;
        char const *end = code + code_size;

        Symbol   **locals = vv(expr_of(ctx->func)->scope->owned);
        Symbol **captures = vv(expr_of(ctx->func)->scope->captured);
        Symbol  **globals = vv(*compiler_globals(ctx->ty));

        TypeHintVector const *hints = &expr_of(ctx->func)->type_hints;

        Type *ARRAY_TYPE = class_get(ty, CLASS_ARRAY)->object_type;

#define BC_READ(var)  do { __builtin_memcpy(&var, ip, sizeof var); ip += sizeof var; } while (0)
#define BC_SKIP(type) (ip += sizeof(type))
#define BC_SKIPSTR()  (ip += strlen(ip) + 1)

        ctx->sp     = 0;
        ctx->max_sp = 0;
        ctx->dead   = false;

        DBG("=========== BEGIN ============");

        while (ip < end) {
                int off = (int)(ip - code);

                Type *hint0 = find_type_hint(hints, off);
                if (hint0 != NULL) {
                        ctx->op_types[ctx->sp - 1] = hint0;
                }

                // If this offset is a jump target, emit label and sync sp + save_sp
                int lbl = bc_find_label(ctx, off);
                if (lbl >= 0) {
                        int target_sp = bc_get_label_sp(ctx, off);
                        if (target_sp >= 0) {
                                // If we're inside a SAVE_STACK_POS region and the
                                // branch target has a different sp than the fall-through
                                // path, the element count between SAVE_STACK_POS and
                                // ARRAY/DICT/etc. can't be determined statically.
                                if (ctx->save_sp_top >= 0 && !ctx->dead && target_sp != ctx->sp) {
                                        ctx->save_sp_divergent[ctx->save_sp_top] = true;
                                }
                                ctx->sp = target_sp;
                        }
                        // Restore save_sp state at this label
                        for (int li = 0; li < ctx->label_count; ++li) {
                                if (ctx->labels[li].offset == off && ctx->labels[li].save_sp_top != -2) {
                                        ctx->save_sp_top = ctx->labels[li].save_sp_top;
                                        memcpy(ctx->save_sp_stack, ctx->labels[li].save_sp_stack,
                                               (ctx->save_sp_top + 1) * sizeof(int));
                                        break;
                                }
                        }
                        ctx->dead = false;
                        jit_emit_label(asm, lbl);
                }

#ifdef TY_PROFILER
                jit_emit_mov(asm, BC_A0, BC_TY);
                jit_emit_load_imm(asm, BC_A1, (iptr)(code + off));
                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_profiler_tick);
                jit_emit_call_reg(asm, BC_CALL);
#endif

                u8 op = (u8)*ip++;

                switch (op) {
                case INSTR_SAVE_STACK_POS:
                case INSTR_DROP_STACK_POS:
                case INSTR_RESTORE_STACK_POS:
                case INSTR_POP_STACK_POS_POP:
                        break;

                case INSTR_JUMP:
                        break;

                default:
                        jit_emit_reload_stack(asm, ctx->bound);
                }

#if JIT_SCAN_LOG
                LOGX(
                        "[jit] [%12.12s] [%16.16s] emit[%4jd] (sp=%2d, #sp_save=%d): %s",
                        expr_of(ctx->func)->mod->name,
                        name_of(ctx->func),
                        ip - code - 1,
                        ctx->sp,
                        ctx->save_sp_top + 1,
                        GetInstructionName(op)
                );
#endif

                switch (op) {
                CASE(NOP)
                        break;

                CASE(LOAD_LOCAL) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        bc_push_from(ctx, BC_LOC, n * VALUE_SIZE);

                        ctx->op_types[ctx->sp - 1] = locals[n]->type;

                        DBG("LOAD_LOCAL %s%s%s (%d)", TERM(93;1), locals[n]->identifier, TERM(0), n);
                        break;
                }

                CASE(ASSIGN_LOCAL) {
                        int n;
                        BC_READ(n);
                        // locals[n] = pop()
                        DBG("ASSIGN_LOCAL");
                        bc_pop_to(ctx, BC_LOC, n * VALUE_SIZE);
                        break;
                }

                CASE(TARGET_LOCAL) {
                        int n;
                        BC_READ(n);
                        // TARGET_LOCAL + ASSIGN fusion:
                        // peek at next instruction
                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++; // consume ASSIGN
                                // locals[n] = peek() (ASSIGN peeks, doesn't pop)
                                bc_copy_value(ctx, BC_LOC, n * VALUE_SIZE, BC_OPS, OP_OFF(ctx->sp - 1));
                        } else if (ip < end && (u8)*ip == INSTR_TRY_ASSIGN_NON_NIL) {
                                ip++; // consume TRY_ASSIGN_NON_NIL
                                int jump;
                                BC_READ(jump);
                                int target_off = (int)(ip - code);
                                // if TOS is nil, jump; else locals[n] = TOS (peek, no pop)
                                int off = OP_OFF(ctx->sp - 1);
                                jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                                int fail_target = target_off + jump;
                                int lbl_nil = bc_label_for(ctx, fail_target);
                                bc_set_label_sp(ctx, fail_target, ctx->sp);
                                jit_emit_branch_eq(asm, lbl_nil);
                                // Not nil: assign TOS to locals[n]
                                bc_copy_value(ctx, BC_LOC, n * VALUE_SIZE, BC_OPS, off);
                        } else if (ip < end && ((u8)*ip == INSTR_MUT_ADD || (u8)*ip == INSTR_MUT_SUB)) {
                                // TARGET_LOCAL + MUT_ADD/MUT_SUB fusion
                                // Addend is on ops stack at sp-1
                                // local[n] += addend, then replace addend with result
                                u8 mut_op = (u8)*ip++;
                                int addend_off = OP_OFF(ctx->sp - 1);
                                int local_off = n * VALUE_SIZE;

                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                // Fast path: check both are VALUE_INTEGER
                                jit_emit_ldrb(asm, BC_S0, BC_LOC, local_off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_branch_ne(asm, lbl_slow);

                                jit_emit_ldrb(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_branch_ne(asm, lbl_slow);

                                // Both integers: load, add/sub, store to local and ops
                                jit_emit_ldr64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);
                                jit_emit_ldr64(asm, BC_S1, BC_OPS, addend_off + VAL_OFF_Z);
                                if (mut_op == INSTR_MUT_ADD) {
                                        jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
                                } else {
                                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                                }
                                // Store result to local
                                jit_emit_str64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);
                                // Store result to ops (replace addend) --- type stays INTEGER
                                jit_emit_str64(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_Z);
                                // Ensure type byte is INTEGER in ops
                                jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_strb(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_TYPE);
                                jit_emit_jump(asm, lbl_done);

                                // Slow path: call runtime helper
                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);                            // arg0: ty
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, local_off);            // arg1: target
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, addend_off);           // arg2: addend
                                jit_emit_mov(asm, BC_A3, BC_A2);                                // arg3: result = addend slot
                                if (mut_op == INSTR_MUT_ADD) {
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_mut_add);
                                } else {
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_mut_sub);
                                }
                                jit_emit_call_reg(asm, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                                // sp unchanged: addend was replaced by result
                        } else if (ip < end && ((u8)*ip == INSTR_MUT_MUL || (u8)*ip == INSTR_MUT_DIV || (u8)*ip == INSTR_MUT_MOD)) {
                                // Deferred target for MUL/DIV/MOD (no integer fast path)
                                ctx->tgt_kind = TGT_LOCAL;
                                ctx->tgt_index = n;
                        } else {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, n * VALUE_SIZE);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_push_target);
                                jit_emit_call_reg(asm, BC_CALL);
                        }
                        break;
                }

                CASE(LOAD_CAPTURED) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        // push(*env[n])
                        // env is Value**, so env[n] is Value*
                        // Load env[n] pointer into S2 (not S0/S1, which bc_copy_value clobbers)
                        jit_emit_ldr64(asm, BC_S2, BC_ENV, n * 8);
                        // Copy the Value it points to
                        bc_push_from(ctx, BC_S2, 0);
                        ctx->op_types[ctx->sp - 1] = captures[n]->type;
                        DBG("LOAD_CAPTURED %s%s%s (%d)", TERM(93;1), captures[n]->identifier, TERM(0), n);
                        break;
                }

                CASE(INT8) {
                        int8_t k = (int8_t)*ip++;

                        // Fusion: INT8 k + SUBSCRIPT => constant-index subscript
                        if (k >= 0 && ip < end && (u8)*ip == INSTR_SUBSCRIPT) {
                                Type *t_con = type_resolve_var(ctx->op_types[ctx->sp - 1]);
                                Class *c = expected_class_of(ctx->ty, t_con);

                                if (c != NULL && c->i == CLASS_TUPLE) {
                                        ip++; // consume SUBSCRIPT

                                        int con_off = OP_OFF(ctx->sp - 1);
                                        int res_off = con_off;
                                        int item_byte_off = k * (int)VALUE_SIZE;

                                        int lbl_slow = bc_next_label(ctx);
                                        int lbl_done = bc_next_label(ctx);

                                        // Check type == VALUE_TUPLE
                                        jit_emit_ldrb(asm, BC_S0, BC_OPS, con_off + VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_TUPLE);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        // Check v.count > k
                                        jit_emit_ldr32(asm, BC_S0, BC_OPS, con_off + VAL_OFF_COUNT);
                                        jit_emit_cmp_ri(asm, BC_S0, k + 1);
                                        jit_emit_branch_lt(asm, lbl_slow);

                                        // Fast: push v.items[k]
                                        jit_emit_ldr64(asm, BC_S1, BC_OPS, con_off + VAL_OFF_ITEMS);
                                        jit_emit_add_imm(asm, BC_S1, BC_S1, item_byte_off);
                                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 0);
                                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off);
                                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 16);
                                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off + 16);
                                        jit_emit_jump(asm, lbl_done);

                                        // Slow: materialize integer, call helper
                                        jit_emit_label(asm, lbl_slow);
                                        int int_off = OP_OFF(ctx->sp);
                                        jit_emit_load_imm(asm, BC_S0, 0);
                                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, int_off);
                                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, int_off + 16);
                                        jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_strb(asm, BC_S0, BC_OPS, int_off + VAL_OFF_TYPE);
                                        jit_emit_load_imm(asm, BC_S0, k);
                                        jit_emit_str64(asm, BC_S0, BC_OPS, int_off + VAL_OFF_Z);
                                        jit_emit_mov(asm, BC_A0, BC_TY);
                                        jit_emit_add_imm(asm, BC_A1, BC_OPS, con_off);
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_subscript);
                                        jit_emit_call_reg(asm, BC_CALL);

                                        jit_emit_label(asm, lbl_done);
                                        // sp unchanged: container replaced by result, no int pushed
                                        break;
                                }

                                // Again for Array
                                if (c != NULL && c->i == CLASS_ARRAY) {
                                        ip++;

                                        int con_off = OP_OFF(ctx->sp - 1);
                                        int res_off = con_off;
                                        int item_byte_off = k * (int)VALUE_SIZE;

                                        int lbl_slow = bc_next_label(ctx);
                                        int lbl_done = bc_next_label(ctx);

                                        // Check v.type == VALUE_ARRAY
                                        jit_emit_ldrb(asm, BC_S0, BC_OPS, con_off + VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_ARRAY);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        // Check vN(*v.array) > k
                                        jit_emit_ldr64(asm, BC_S1, BC_OPS, con_off + VAL_OFF_Z);
                                        jit_emit_ldr64(asm, BC_S2, BC_S1, OFF_VEC_LEN);
                                        jit_emit_cmp_ri(asm, BC_S2, k + 1);
                                        jit_emit_branch_lt(asm, lbl_slow);

                                        // Fast: push v__(*v.array, k)
                                        jit_emit_ldr64(asm, BC_S1, BC_S1, 0);
                                        jit_emit_add_imm(asm, BC_S1, BC_S1, item_byte_off);
                                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 0);
                                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off);
                                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 16);
                                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off + 16);
                                        jit_emit_jump(asm, lbl_done);

                                        // Slow: materialize integer, call helper
                                        jit_emit_label(asm, lbl_slow);
                                        int int_off = OP_OFF(ctx->sp);
                                        jit_emit_load_imm(asm, BC_S0, 0);
                                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, int_off);
                                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, int_off + 16);
                                        jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_strb(asm, BC_S0, BC_OPS, int_off + VAL_OFF_TYPE);
                                        jit_emit_load_imm(asm, BC_S0, k);
                                        jit_emit_str64(asm, BC_S0, BC_OPS, int_off + VAL_OFF_Z);
                                        jit_emit_mov(asm, BC_A0, BC_TY);
                                        jit_emit_add_imm(asm, BC_A1, BC_OPS, con_off);
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_subscript);
                                        jit_emit_call_reg(asm, BC_CALL);

                                        jit_emit_label(asm, lbl_done);
                                        // sp unchanged: container replaced by result, no int pushed
                                        break;
                                }
                        }

                        bc_push_integer(ctx, k);
                        break;
                }

                CASE(INTEGER) {
                        imax k;
                        BC_READ(k);
                        bc_push_integer(ctx, k);
                        break;
                }

                CASE(TRUE)
                        bc_push_bool(ctx, true);
                        break;

                CASE(FALSE)
                        bc_push_bool(ctx, false);
                        break;

                CASE(NIL)
                        bc_push_nil(ctx);
                        break;

                CASE(SENTINEL) {
                        int dst = OP_OFF(ctx->sp);
                        jit_emit_load_imm(asm, BC_S0, VALUE_SENTINEL);
                        jit_emit_strb(asm, BC_S0, BC_OPS, dst + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 8);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 16);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 24);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(NONE) {
                        int dst = OP_OFF(ctx->sp);
                        jit_emit_load_imm(asm, BC_S0, VALUE_NONE);
                        jit_emit_strb(asm, BC_S0, BC_OPS, dst + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 8);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 16);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 24);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(OPERATOR) {
                        int u_op;
                        int b_op;
                        BC_READ(u_op);
                        BC_READ(b_op);
                        int dst = OP_OFF(ctx->sp);
                        jit_emit_load_imm(asm, BC_S0, VALUE_OPERATOR);
                        jit_emit_strb(asm, BC_S0, BC_OPS, dst + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, u_op);
                        jit_emit_str32(asm, BC_S0, BC_OPS, dst + VAL_OFF_UOP);
                        jit_emit_load_imm(asm, BC_S0, b_op);
                        jit_emit_str32(asm, BC_S0, BC_OPS, dst + VAL_OFF_BOP);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(POP)
                        ctx->sp--;
                        break;

                CASE(POP2)
                        ctx->sp -= 2;
                        break;

                CASE(DUP)
                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_OPS, OP_OFF(ctx->sp - 1));
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;

                CASE(SWAP) {
                        // Swap ops[sp-1] and ops[sp-2]
                        int a = OP_OFF(ctx->sp - 1);
                        int b = OP_OFF(ctx->sp - 2);
                        // Load a into S0,S1
                        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, a);
                        jit_emit_ldp64(asm, BC_S2, BC_S3, BC_OPS, a + 16);
                        // Load b into temp via direct copy
                        // Copy b -> a
                        bc_copy_value(ctx, BC_OPS, a, BC_OPS, b);
                        // Store original a (in regs) to b
                        jit_emit_stp64(asm, BC_S0, BC_S1, BC_OPS, b);
                        jit_emit_stp64(asm, BC_S2, BC_S3, BC_OPS, b + 16);
                        break;
                }

                CASE(ADD)
                        bc_emit_arith(ctx, (void *)jit_rt_add);
                        break;

                CASE(SUB)
                        bc_emit_arith(ctx, (void *)jit_rt_sub);
                        break;

                CASE(MUL)
                        bc_emit_arith(ctx, (void *)jit_rt_mul);
                        break;

                CASE(DIV)
                        bc_emit_arith(ctx, (void *)jit_rt_div);
                        break;

                CASE(MOD)
                        bc_emit_arith(ctx, (void *)jit_rt_mod);
                        break;

                CASE(NEG) {
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        // Fast: negate in place
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_neg(asm, BC_S0, BC_S0);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_jump(asm, lbl_done);

                        jit_emit_label(asm, lbl_slow);
                        bc_emit_unop_helper(ctx, (void *)jit_rt_neg);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(NOT) {
                        // !value: for booleans, flip; for nil, true; for int, z==0; else call helper
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_bool = bc_next_label(ctx);
                        int lbl_nil  = bc_next_label(ctx);
                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

                        jit_emit_cmp_ri(asm, BC_S0, VALUE_BOOLEAN);
                        jit_emit_branch_eq(asm, lbl_bool);

                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                        jit_emit_branch_eq(asm, lbl_nil);

                        // Slow path
                        jit_emit_label(asm, lbl_slow);
                        bc_emit_unop_helper(ctx, (void *)jit_rt_not);
                        jit_emit_jump(asm, lbl_done);

                        // BOOL: flip z (0=>1, 1=>0), keep type as BOOLEAN
                        jit_emit_label(asm, lbl_bool);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_load_imm(asm, BC_S1, 1);
                        jit_emit_xor(asm, BC_S0, BC_S0, BC_S1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_jump(asm, lbl_done);

                        // NIL: result = true
                        jit_emit_label(asm, lbl_nil);
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_BOOLEAN);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, 1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(EQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_eq);
                        break;

                CASE(NEQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_ne);
                        break;

                CASE(LT)
                        bc_emit_cmp(ctx, (void *)jit_rt_lt);
                        break;

                CASE(GT)
                        bc_emit_cmp(ctx, (void *)jit_rt_gt);
                        break;

                CASE(LEQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_le);
                        break;

                CASE(GEQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_ge);
                        break;

                CASE(JUMP) {
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl = bc_find_label(ctx, target);
                        if (lbl < 0) BAIL("invalid jump target %d", target);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_jump(asm, lbl);
                        ctx->dead = true;
                        break;
                }

                CASE(JUMP_IF) {
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid jump target %d", target);

                        // Check truthiness of TOS, pop
                        bc_emit_truthy(ctx);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);

                        // Branch if truthy (BC_S0 != 0)
                        jit_emit_cbnz(asm, BC_S0, lbl_target);
                        break;
                }

                CASE(JUMP_IF_NOT) {
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid jump target %d", target);

                        bc_emit_truthy(ctx);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);

                        // Branch if NOT truthy (BC_S0 == 0)
                        jit_emit_cbz(asm, BC_S0, lbl_target);
                        break;
                }

                CASE(JUMP_IF_NIL) {
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid jump target %d", target);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp - 1) + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, lbl_target);
                        break;
                }

                CASE(JUMP_IF_NONE) {
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid jump target %d", target);

                        int tos_off = OP_OFF(ctx->sp - 1);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, tos_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NONE);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, lbl_target);
                        break;
                }

                CASE(JUMP_AND) {
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid jump target %d", target);

                        // If TOS is falsy, jump (keep TOS)
                        // If truthy, pop and continue
                        bc_emit_truthy(ctx); // result in BC_S0
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_cbz(asm, BC_S0, lbl_target);
                        // Truthy: pop
                        ctx->sp--;
                        break;
                }

                CASE(JUMP_OR) {
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid jump target %d", target);

                        // If TOS is truthy, jump (keep TOS)
                        // If falsy, pop and continue
                        bc_emit_truthy(ctx);
                        bc_set_label_sp(ctx, target, ctx->sp); // TOS kept at branch target
                        // If truthy, jump
                        jit_emit_cbnz(asm, BC_S0, lbl_target);
                        DBG("JUMP_OR: falsy, continue");
                        // Falsy: pop
                        ctx->sp--;
                        break;
                }

                CASE(JEQ)
                CASE(JNE) {
                        char const *op_ip = code + off;
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid jump target %d", target);

                        int a_off = OP_OFF(ctx->sp - 2);
                        int b_off = OP_OFF(ctx->sp - 1);
                        bool is_eq = (op == INSTR_JEQ);

                        Class *cls = expected_class_of(ctx->ty, ctx->op_types[ctx->sp - 1]);

                        int lbl_nil_check = bc_next_label(ctx);
                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        // Load both types
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, a_off + VAL_OFF_TYPE); // a.type
                        jit_emit_ldrb(asm, BC_S1, BC_OPS, b_off + VAL_OFF_TYPE); // b.type

                        if (cls != NULL && cls->i == CLASS_INT) {
                                // === Integer fast path ===
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_branch_ne(asm, lbl_nil_check);

                                jit_emit_cmp_ri(asm, BC_S1, VALUE_INTEGER);
                                jit_emit_branch_ne(asm, lbl_slow);

                                EMIT_STAT(jit_rt_stat_jeq_int);
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, a_off + VAL_OFF_Z);
                                jit_emit_ldr64(asm, BC_S1, BC_OPS, b_off + VAL_OFF_Z);
                                jit_emit_cmp_rr(asm, BC_S0, BC_S1);
                                if (is_eq)
                                        jit_emit_branch_eq(asm, lbl_target);
                                else
                                        jit_emit_branch_ne(asm, lbl_target);
                                jit_emit_jump(asm, lbl_done);
                        } else if (cls != NULL && cls->i == CLASS_STRING) {
                                // === String fast path ===
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_STRING);
                                jit_emit_branch_ne(asm, lbl_nil_check);

                                jit_emit_cmp_ri(asm, BC_S1, VALUE_STRING);
                                jit_emit_branch_ne(asm, lbl_slow);

                                EMIT_STAT(jit_rt_stat_jeq_str);
                                jit_emit_add_imm(asm, BC_A0, BC_OPS, a_off);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, b_off);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_str_eq);
                                jit_emit_call_reg(asm, BC_CALL);
                                // Return value in register 0
                                if (is_eq)
                                        jit_emit_cbnz(asm, BC_RET, lbl_target);
                                else
                                        jit_emit_cbz(asm, BC_RET, lbl_target);
                                jit_emit_jump(asm, lbl_done);
                        }

                        // === Nil fast path ===
                        jit_emit_label(asm, lbl_nil_check);
                        // Reload types (EMIT_STAT or call may have clobbered them,
                        // or we fell through with no fast path and they're still valid,
                        // but reloading is cheap and safe in all cases)
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, a_off + VAL_OFF_TYPE);
                        jit_emit_ldrb(asm, BC_S1, BC_OPS, b_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                        int lbl_a_nil = bc_next_label(ctx);
                        jit_emit_branch_eq(asm, lbl_a_nil);
                        jit_emit_cmp_ri(asm, BC_S1, VALUE_NIL);
                        jit_emit_branch_ne(asm, lbl_slow);
                        // b is nil, a is not nil: EQ=false(no branch), NEQ=true(branch)
                        EMIT_STAT(jit_rt_stat_jeq_nil);
                        if (!is_eq)
                                jit_emit_jump(asm, lbl_target);
                        jit_emit_jump(asm, lbl_done);
                        // a is nil
                        jit_emit_label(asm, lbl_a_nil);
                        EMIT_STAT(jit_rt_stat_jeq_nil);
                        // result = (b.type == VALUE_NIL) --- reload b.type
                        jit_emit_ldrb(asm, BC_S1, BC_OPS, b_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S1, VALUE_NIL);
                        if (is_eq)
                                jit_emit_branch_eq(asm, lbl_target);
                        else
                                jit_emit_branch_ne(asm, lbl_target);
                        jit_emit_jump(asm, lbl_done);

                        // === Slow path: call helper ===
                        jit_emit_label(asm, lbl_slow);
                        EMIT_SLOW2(op_ip, SLOW_JEQ, BC_OPS, a_off, BC_OPS, b_off);
                        void *helper = is_eq ? (void *)jit_rt_eq : (void *)jit_rt_ne;
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, a_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, a_off);
                        jit_emit_add_imm(asm, BC_A3, BC_OPS, b_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)helper);
                        jit_emit_call_reg(asm, BC_CALL);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, a_off + VAL_OFF_BOOL);
                        jit_emit_cbnz(asm, BC_S0, lbl_target);

                        jit_emit_label(asm, lbl_done);
                        ctx->sp -= 2;
                        bc_set_label_sp(ctx, target, ctx->sp);
                        break;
                }

                CASE(JLT)
                CASE(JGT)
                CASE(JLE)
                CASE(JGE) {
                        char const *op_ip = code + off;
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid jump target %d", target);

                        int a_off = OP_OFF(ctx->sp - 2);
                        int b_off = OP_OFF(ctx->sp - 1);

                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        // Load both types
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, a_off + VAL_OFF_TYPE);
                        jit_emit_ldrb(asm, BC_S1, BC_OPS, b_off + VAL_OFF_TYPE);

                        // Check a.type == VALUE_INTEGER
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        // Check b.type == VALUE_INTEGER
                        jit_emit_cmp_ri(asm, BC_S1, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        // === Integer fast path: compare a.z vs b.z ===
                        EMIT_STAT(jit_rt_stat_jcmp_int);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, a_off + VAL_OFF_Z);
                        jit_emit_ldr64(asm, BC_S1, BC_OPS, b_off + VAL_OFF_Z);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
                        switch (op) {
                        case INSTR_JLT: jit_emit_branch_lt(asm, lbl_target); break;
                        case INSTR_JGT: jit_emit_branch_gt(asm, lbl_target); break;
                        case INSTR_JLE: jit_emit_branch_le(asm, lbl_target); break;
                        case INSTR_JGE: jit_emit_branch_ge(asm, lbl_target); break;
                        }
                        jit_emit_jump(asm, lbl_done);

                        // === Slow path: call jit_rt_compare(ty, &a, &b) ===
                        jit_emit_label(asm, lbl_slow);
                        EMIT_SLOW2(op_ip, SLOW_JCMP, BC_OPS, a_off, BC_OPS, b_off);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, a_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, b_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_compare);
                        jit_emit_call_reg(asm, BC_CALL);

                        // Result in w0: <0, 0, >0 (int, 32-bit)
                        jit_emit_cmp_ri32(asm, BC_RET, 0);
                        switch (op) {
                        case INSTR_JLT: jit_emit_branch_lt(asm, lbl_target); break;
                        case INSTR_JGT: jit_emit_branch_gt(asm, lbl_target); break;
                        case INSTR_JLE: jit_emit_branch_le(asm, lbl_target); break;
                        case INSTR_JGE: jit_emit_branch_ge(asm, lbl_target); break;
                        }

                        jit_emit_label(asm, lbl_done);
                        ctx->sp -= 2;
                        bc_set_label_sp(ctx, target, ctx->sp);
                        break;
                }

                CASE(MEMBER_ACCESS) {
                        char const *op_ip = code + off;
                        int z;
                        BC_READ(z);

                        // Try type-guided fast path using local type info
                        Type *t0 = ctx->op_types[ctx->sp - 1];
                        Class *obj_class = expected_class_of(ctx->ty, t0);

                        bool emitted_fast = false;
                        if (obj_class != NULL) {
                                Ty *ty = ctx->ty;
                                if (z < (int)vN(obj_class->offsets_r)) {
                                        u16 off = v__(obj_class->offsets_r, z);
                                        if (off != OFF_NOT_FOUND && (off >> OFF_SHIFT) == OFF_FIELD) {
                                                u16 slot_idx = off & OFF_MASK;
                                                int class_id = obj_class->i;
                                                int slot_byte_off = OBJ_OFF_SLOTS + slot_idx * VALUE_SIZE;

                                                if (slot_byte_off + 16 <= 504) {
                                                        int obj_off = OP_OFF(ctx->sp - 1);
                                                        int lbl_slow = bc_next_label(ctx);
                                                        int lbl_done = bc_next_label(ctx);

                                                        // Check obj.type == VALUE_OBJECT
                                                        jit_emit_ldrb(asm, BC_S0, BC_OPS, obj_off + VAL_OFF_TYPE);
                                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_OBJECT);
                                                        jit_emit_branch_ne(asm, lbl_slow);

                                                        // Check obj.class == expected
                                                        jit_emit_ldr32(asm, BC_S0, BC_OPS, obj_off + VAL_OFF_CLASS);
                                                        jit_emit_cmp_ri(asm, BC_S0, class_id);
                                                        jit_emit_branch_ne(asm, lbl_slow);

                                                        // Fast: load obj.object => BC_S2, copy slot to ops
                                                        EMIT_STAT(jit_rt_stat_member_fast);
                                                        jit_emit_ldr64(asm, BC_S2, BC_OPS, obj_off + VAL_OFF_OBJECT);
                                                        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off);
                                                        jit_emit_stp64(asm, BC_S0, BC_S1, BC_OPS, obj_off);
                                                        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off + 16);
                                                        jit_emit_stp64(asm, BC_S0, BC_S1, BC_OPS, obj_off + 16);
                                                        jit_emit_jump(asm, lbl_done);

                                                        // Slow: call helper
                                                        jit_emit_label(asm, lbl_slow);
                                                        EMIT_SLOW1(op_ip, SLOW_MEMBER_ACCESS, BC_OPS, obj_off);
                                                        jit_emit_mov(asm, BC_A0, BC_TY);
                                                        jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);
                                                        jit_emit_mov(asm, BC_A2, BC_A1);
                                                        jit_emit_load_imm(asm, BC_A3, z);
                                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
                                                        jit_emit_call_reg(asm, BC_CALL);

                                                        jit_emit_label(asm, lbl_done);
                                                        emitted_fast = true;
                                                }
                                        }
                                }
                        }

                        if (!emitted_fast) {
                                // Generic path (no type info --- not trapped)
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp - 1));
                                jit_emit_mov(asm, BC_A2, BC_A1);
                                jit_emit_load_imm(asm, BC_A3, z);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
                                jit_emit_call_reg(asm, BC_CALL);
                        }

                        DBG("MEMBER_ACCESS");
                        break;
                }

                CASE(SELF_MEMBER_ACCESS) {
                        char const *op_ip = code + off;
                        int z;
                        BC_READ(z);

                        // Try type-guided fast path (baked slot offset)
                        if (bc_emit_self_member_read_fast(ctx, z, op_ip)) {
                                break;
                        }

                        Type *t0 = (ctx->self_class != NULL)
                                 ? ctx->self_class->object_type
                                 : NULL;

                        ctx->sp++; // make room for result (helper will write to sp-1)

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp - 1));
                        jit_emit_load_imm(asm, BC_A2, 0);
                        jit_emit_load_imm(asm, BC_A3, z);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
                        jit_emit_call_reg(asm, BC_CALL);

                        DBG("SELF_MEMBER_ACCESS");
                        break;
                }

                CASE(TARGET_MEMBER) {
                        char const *op_ip = code + off;
                        int z;
                        BC_READ(z);

                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++; // consume ASSIGN
                                // Stack: [... val obj] where obj is on top (sp-1)
                                // val is at sp-2
                                // TARGET_MEMBER pops obj, ASSIGN peeks val (doesn't pop)

                                // Try type-guided fast path
                                Class *obj_class = expected_class_of(ctx->ty, ctx->op_types[ctx->sp - 1]);

                                bool wrote_fast = false;
                                if (obj_class != NULL) {
                                        Ty *ty = ctx->ty;
                                        if (z < (int)vN(obj_class->offsets_w)) {
                                                u16 off = v__(obj_class->offsets_w, z);
                                                if (off != OFF_NOT_FOUND && (off >> OFF_SHIFT) == OFF_FIELD) {
                                                        u16 slot_idx = off & OFF_MASK;
                                                        int class_id = obj_class->i;
                                                        int slot_byte_off = OBJ_OFF_SLOTS + slot_idx * VALUE_SIZE;

                                                        if (slot_byte_off + 16 <= 504) {
                                                                int obj_off = OP_OFF(ctx->sp - 1);
                                                                int val_off = OP_OFF(ctx->sp - 2);
                                                                int lbl_slow = bc_next_label(ctx);
                                                                int lbl_done = bc_next_label(ctx);

                                                                // Check obj.type == VALUE_OBJECT
                                                                jit_emit_ldrb(asm, BC_S0, BC_OPS, obj_off + VAL_OFF_TYPE);
                                                                jit_emit_cmp_ri(asm, BC_S0, VALUE_OBJECT);
                                                                jit_emit_branch_ne(asm, lbl_slow);

                                                                // Check obj.class == expected
                                                                jit_emit_ldr32(asm, BC_S0, BC_OPS, obj_off + VAL_OFF_CLASS);
                                                                jit_emit_cmp_ri(asm, BC_S0, class_id);
                                                                jit_emit_branch_ne(asm, lbl_slow);

                                                                // Fast: load obj.object => BC_S2, copy val to slot
                                                                EMIT_STAT(jit_rt_stat_member_set_fast);
                                                                jit_emit_ldr64(asm, BC_S2, BC_OPS, obj_off + VAL_OFF_OBJECT);
                                                                jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, val_off);
                                                                jit_emit_stp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off);
                                                                jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, val_off + 16);
                                                                jit_emit_stp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off + 16);
                                                                jit_emit_jump(asm, lbl_done);

                                                                // Slow: call helper
                                                                jit_emit_label(asm, lbl_slow);
                                                                EMIT_SLOW1(op_ip, SLOW_MEMBER_SET, BC_OPS, obj_off);
                                                                jit_emit_mov(asm, BC_A0, BC_TY);
                                                                jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);
                                                                jit_emit_load_imm(asm, BC_A2, z);
                                                                jit_emit_add_imm(asm, BC_A3, BC_OPS, val_off);
                                                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member_set);
                                                                jit_emit_call_reg(asm, BC_CALL);

                                                                jit_emit_label(asm, lbl_done);
                                                                wrote_fast = true;
                                                        }
                                                }
                                        }
                                }

                                if (!wrote_fast) {
                                        jit_emit_mov(asm, BC_A0, BC_TY);
                                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp - 1));
                                        jit_emit_load_imm(asm, BC_A2, z);
                                        jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp - 2));
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member_set);
                                        jit_emit_call_reg(asm, BC_CALL);
                                }
                                ctx->sp -= 1; // only pop obj, val stays
                        } else {
                                // Deferred target: record for later MUT_ADD/MUT_SUB.
                                // obj is at sp-1. We "pop" it but remember where it was
                                // so MUT_ADD can pass it to the runtime helper.
                                ctx->tgt_kind = TGT_MEMBER;
                                ctx->tgt_index = z;
                                ctx->tgt_obj_sp = ctx->sp - 1; // obj slot (still valid in memory)
                                ctx->sp -= 1; // pop obj
                        }
                        break;
                }

                CASE(TARGET_SELF_MEMBER) {
                        char const *op_ip = code + off;
                        int z;
                        BC_READ(z);

                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++; // consume ASSIGN

                                // Try type-guided fast path
                                if (bc_emit_self_member_write_fast(ctx, z, op_ip)) {
                                        break;
                                }

                                // Generic path: call helper
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_load_imm(asm, BC_A1, 0);
                                jit_emit_load_imm(asm, BC_A2, z);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp - 1));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member_set);
                                jit_emit_call_reg(asm, BC_CALL);
                                // val stays on stack (ASSIGN peeks, doesn't pop)
                        } else {
                                // Deferred target for later MUT_ADD/MUT_SUB
                                ctx->tgt_kind = TGT_SELF_MEMBER;
                                ctx->tgt_index = z;
                                // No obj pop --- self is implicit in locals[param_count]
                        }
                        break;
                }

                CASE(TARGET_SUBSCRIPT) {
                        // Stack: [..., container, subscript] -> pops both
                        // Record for deferred mutation
                        ctx->tgt_kind = TGT_SUBSCRIPT;
                        ctx->tgt_obj_sp = ctx->sp - 2; // container position
                        ctx->tgt_index = ctx->sp - 1;  // subscript position (reusing field)
                        ctx->sp -= 2;
                        break;
                }

                CASE(ASSIGN)
                        // Standalone ASSIGN (not fused) --- bail
                        BAIL("standalone ASSIGN not supported");

                CASE(CALL) {
                        int n, nkw;
                        BC_READ(n);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (nkw > 0) {
                                BAIL("CALL with kwargs not supported");
                        }

                        if (n == -1) {
                                BAIL("CALL with spread args not supported");
                        }

                        Type *f0 = ctx->op_types[ctx->sp - 1];

                        DBG("CALL(argc=%d)", n);

                        // fn is still at ops[sp-1]
                        // Result overwrites the fn slot, args+fn all consumed => sp -= (n+1), push result => sp += 1
                        int fn_off = OP_OFF(ctx->sp - 1);
                        int result_off = OP_OFF(ctx->sp - n - 1);

                        // Sync the Ty stack count so the helper can set up the callee's frame
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);

                        // Use trampoline-aware helper: returns 0 if handled, 1 if callee is JIT
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);  // result
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, fn_off);      // fn
                        jit_emit_load_imm(asm, BC_A3, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_trampoline);
                        jit_emit_call_reg(asm, BC_CALL);

                        // Check return: 0 = handled inline, 1 = JIT callee pending
                        int lbl_done = bc_next_label(ctx);
                        jit_emit_cbz(asm, BC_RET, lbl_done);

                        // JIT callee detected: save resume index, signal trampoline, return
                        int site_idx = ctx->call_site_count++;
                        int resume_lbl = bc_next_label(ctx);
                        ctx->resume_labels[site_idx] = resume_lbl;

                        jit_emit_load_imm(asm, BC_S0, JIT_CALL);
                        jit_emit_str32(asm, BC_S0, BC_TY, OFF_JIT_STATUS);
                        jit_emit_load_imm(asm, BC_S0, site_idx + 1); // 1-based resume index
                        jit_emit_str32(asm, BC_S0, BC_TY, OFF_JIT_SAVED_RES);

                        // Jump to epilogue (return to trampoline)
                        int lbl_ret = bc_label_for(ctx, -1);
                        jit_emit_jump(asm, lbl_ret);

                        // Resume label: entered when trampoline re-invokes us
                        // The callee's result is already on the Ty stack at the correct position.
                        // Registers will be reloaded at the next instruction's top-of-loop reload.
                        jit_emit_label(asm, resume_lbl);

                        // Join point for both paths
                        jit_emit_label(asm, lbl_done);

                        // Pop fn + n args, push result
                        ctx->sp -= n; // was n+1 slots (args+fn), now 1 slot (result)
                        DBG("CALL");
                        break;
                }

                CASE(CALL_METHOD) {
                        char const *op_ip = code + off;
                        int n, z, nkw;
                        BC_READ(n);
                        BC_READ(z);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (nkw > 0 || n == -1) {
                                BAIL("CALL_METHOD with kwargs/spread not supported");
                        }

                        bc_emit_call_method(ctx, op_ip, z, n, nkw);
                        break;
                }

                CASE(CALL_SELF_METHOD) {
                        char const *op_ip = code + off;
                        int n, z, nkw;
                        BC_READ(n);
                        BC_READ(z);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        EMIT_SET_CALL_IP(op_ip);

                        if (nkw > 0 || n == -1) {
                                BAIL("CALL_SELF_METHOD with kwargs/spread not supported");
                        }

                        // Try builtin type fast path (String, Array, Dict, Blob)
                        int builtin_vtype = -1;
                        BuiltinMethod *builtin_method = bc_resolve_builtin_method(
                                ctx->self_class,
                                z,
                                &builtin_vtype
                        );

                        // Try object method baking (for user-defined classes)
                        Value *baked_method = bc_resolve_method(ctx, ctx->self_class, z);

                        // For CALL_SELF_METHOD, self is implicit (not on operand stack).
                        // Operand stack: [...][arg0][arg1]...[argN-1]
                        // Result replaces args: goes at ops[sp - n]
                        int result_off = OP_OFF(ctx->sp - n);

                        if (builtin_method != NULL) {
                                // Direct builtin call with type guard
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                jit_emit_load_imm(asm, BC_A2, 0);
                                jit_emit_load_imm(asm, BC_A3, (iptr)builtin_method);
                                jit_emit_load_imm(asm, BC_A4, PACK32(builtin_vtype, z));
                                jit_emit_load_imm(asm, BC_A5, n);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_builtin_method);
                                jit_emit_call_reg(asm, BC_CALL);
                                DBG("CALL_METHOD (builtin fast path for %s)", M_NAME(z));
                        } else if (baked_method != NULL) {
                                // Guarded fast path for user-defined classes
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                jit_emit_load_imm(asm, BC_A2, 0);
                                jit_emit_load_imm(asm, BC_A3, (iptr)baked_method);
                                jit_emit_load_imm(asm, BC_A4, PACK32(ctx->self_class->i, z));
                                jit_emit_load_imm(asm, BC_A5, n);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_self_method_guarded);
                                jit_emit_call_reg(asm, BC_CALL);
                        } else {
                                // Generic path: runtime method lookup
                                // self=NULL tells jit_rt_call_method to use vm_get_self
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);  // result
                                jit_emit_load_imm(asm, BC_A2, 0);                  // self = NULL
                                jit_emit_load_imm(asm, BC_A3, z);                  // member_id
                                jit_emit_load_imm(asm, BC_A4, n);                  // argc
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_method);
                                jit_emit_call_reg(asm, BC_CALL);
                        }

                        // n args consumed, 1 result produced
                        ctx->sp -= (n - 1);
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(CALL_GLOBAL) {
                        int gi, n, nkw;
                        BC_READ(gi);
                        BC_READ(n);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (nkw > 0 || n == -1) {
                                BAIL("CALL_GLOBAL with kwargs/spread not supported");
                        }

                        DBG("CALL_GLOBAL(%s, argc=%d)", VSC(vm_global(ty, gi)), n);

                        ctx->sp -= n;

                        // Sync the Ty stack count
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp + n);

                        // If the global is a const builtin function, emit a direct call
                        if (SymbolIsConst(globals[gi]) && v_(Globals, gi)->type == VALUE_BUILTIN_FUNCTION) {
                                BuiltinFunction *fn = v_(Globals, gi)->builtin_function;
                                int result_off = OP_OFF(ctx->sp);

                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                jit_emit_load_imm(asm, BC_A2, (iptr)fn);
                                jit_emit_load_imm(asm, BC_A3, n);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_builtin_function);
                                jit_emit_call_reg(asm, BC_CALL);

                                DBG("CALL_GLOBAL(%s) [direct builtin]", VSC(vm_global(ty, gi)));

                                ctx->sp++;
                                if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                                break;
                        }

                        // Try fast trampoline path (skips xcall overhead)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_A1, gi);
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_fast_global_call);
                        jit_emit_call_reg(asm, BC_CALL);

                        int lbl_cg_slow = bc_next_label(ctx);
                        int lbl_cg_done = bc_next_label(ctx);

                        // If return 0: not JIT'd or not simple, use slow path
                        jit_emit_cbz(asm, BC_RET, lbl_cg_slow);

                        // Fast path handled: result already on stack, skip slow path
                        jit_emit_jump(asm, lbl_cg_done);

                        // Slow fallback: load global + call trampoline
                        jit_emit_label(asm, lbl_cg_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_A1, gi);
                        jit_emit_load_imm(asm, BC_S0, (iptr)vm_global);
                        jit_emit_call_reg(asm, BC_S0);
                        // x0 now has Value* to the global
                        jit_emit_mov(asm, BC_A2, BC_RET);  // fn ptr (was in x0)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp)); // result
                        jit_emit_load_imm(asm, BC_A3, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_trampoline);
                        jit_emit_call_reg(asm, BC_CALL);

                        // Old trampoline may also signal JIT_CALL
                        int lbl_cg_done2 = bc_next_label(ctx);
                        jit_emit_cbz(asm, BC_RET, lbl_cg_done2);

                        int cg_site_idx2 = ctx->call_site_count++;
                        int cg_resume_lbl2 = bc_next_label(ctx);
                        ctx->resume_labels[cg_site_idx2] = cg_resume_lbl2;

                        jit_emit_load_imm(asm, BC_S0, JIT_CALL);
                        jit_emit_str32(asm, BC_S0, BC_TY, OFF_JIT_STATUS);
                        jit_emit_load_imm(asm, BC_S0, cg_site_idx2 + 1);
                        jit_emit_str32(asm, BC_S0, BC_TY, OFF_JIT_SAVED_RES);

                        int lbl_cg_ret2 = bc_label_for(ctx, -1);
                        jit_emit_jump(asm, lbl_cg_ret2);

                        jit_emit_label(asm, cg_resume_lbl2);
                        jit_emit_label(asm, lbl_cg_done2);

                        jit_emit_label(asm, lbl_cg_done);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;

                        DBG("CALL_GLOBAL(%s)", VSC(vm_global(ty, gi)));
                        break;
                }

                CASE(RETURN)
                CASE(RETURN_PRESERVE_CTX) {
                        // Result is ops[sp-1], copy to *BC_RES
                        bc_copy_value(ctx, BC_RES, 0, BC_OPS, OP_OFF(ctx->sp - 1));

                        // Jump to shared epilogue
                        int lbl_ret = bc_label_for(ctx, -1);
                        jit_emit_jump(asm, lbl_ret);
                        ctx->dead = true;
                        break;
                }

                CASE(RETURN_IF_NOT_NONE) {
                        // If TOS is not NONE, return it
                        int top_off = OP_OFF(ctx->sp - 1);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, top_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NONE);
                        int lbl_skip = bc_next_label(ctx);
                        jit_emit_branch_eq(asm, lbl_skip);
                        // Not NONE --- return this value
                        bc_copy_value(ctx, BC_RES, 0, BC_OPS, top_off);
                        int lbl_ret = bc_label_for(ctx, -1);
                        jit_emit_jump(asm, lbl_ret);
                        jit_emit_label(asm, lbl_skip);
                        break;
                }

                CASE(HALT)
                        break;

                CASE(LOAD_GLOBAL) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        // Load global[n]
                        jit_emit_load_imm(asm, BC_S2, (iptr)&Globals);
                        jit_emit_ldr64(asm, BC_S3, BC_S2, OFF_VEC_DATA);
                        bc_push_from(ctx, BC_S3, n * sizeof (Value));
                        ctx->op_types[ctx->sp - 1] = globals[n]->type;
                        DBG("LOAD_GLOBAL %s (%d)", compiler_global_sym(ty, n)->identifier, n);
                        break;
                }

                CASE(LOAD_THREAD_LOCAL) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        int lbl_slow = bc_next_label(ctx);
                        int lbl_fast = bc_next_label(ctx);
                        jit_emit_ldr64(asm, BC_S0, BC_TY, OFF_TY_TLS + OFF_VEC_LEN);
                        jit_emit_cmp_ri(asm, BC_S0, n);
                        jit_emit_branch_le(asm, lbl_slow);
                        jit_emit_ldr64(asm, BC_S3, BC_TY, OFF_TY_TLS + OFF_VEC_DATA);
                        jit_emit_ldrb(asm, BC_S0, BC_S3, n * sizeof (Value) + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NONE);
                        jit_emit_branch_ne(asm, lbl_fast);
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_tls0);
                        jit_emit_call_reg(asm, BC_CALL);
                        jit_emit_ldr64(asm, BC_S3, BC_TY, OFF_TY_TLS + OFF_VEC_DATA);
                        jit_emit_label(asm, lbl_fast);
                        bc_push_from(ctx, BC_S3, n * sizeof (Value));
                        break;
                }

                CASE(VALUE) {
                        uptr p;
                        BC_READ(p);
                        jit_emit_load_imm(asm, BC_S2, (iptr)p);
                        bc_push_from(ctx, BC_S2, 0);
                        break;
                }

                CASE(TYPE) {
                        uptr p;
                        BC_READ(p);
                        int off = OP_OFF(ctx->sp);
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_TYPE);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, (iptr)p);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(REGEX) {
                        uptr p;
                        BC_READ(p);
                        int off = OP_OFF(ctx->sp);
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_REGEX);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, (iptr)p);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_REGEX);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(SAVE_STACK_POS)
                        // Push current sp onto compile-time save stack
                        if (ctx->save_sp_top >= 15) BAIL("SAVE_STACK_POS stack overflow");
                        ++ctx->save_sp_top;
                        ctx->save_sp_stack[ctx->save_sp_top] = ctx->sp;
                        ctx->save_sp_divergent[ctx->save_sp_top] = false;
                        SAVE_STACK_POS();
                        break;
                CASE(RESTORE_STACK_POS)
                        // Restore compile-time sp (without popping save stack)
                        if (ctx->save_sp_top >= 0) {
                                ctx->sp = ctx->save_sp_stack[ctx->save_sp_top];
                        }
                        RESTORE_STACK_POS();
                        break;
                CASE(POP_STACK_POS)
                        // Restore compile-time sp
                        if (ctx->save_sp_top < 0) {
                                if (ctx->dead) break;
                                BAIL("POP_STACK_POS stack underflow");
                        }
                        ctx->sp = ctx->save_sp_stack[ctx->save_sp_top--];
                        POP_STACK_POS(0);
                        break;
                CASE(POP_STACK_POS_POP)
                        // Restore compile-time sp - 1
                        if (ctx->save_sp_top < 0) {
                                if (ctx->dead) break;
                                BAIL("POP_STACK_POS_POP stack underflow");
                        }
                        ctx->sp = ctx->save_sp_stack[ctx->save_sp_top--] - 1;
                        POP_STACK_POS(1);
                        break;

                CASE(ARRAY) {
                        if (ctx->save_sp_top < 0) BAIL("ARRAY requires SAVE_STACK_POS");
                        if (ctx->save_sp_divergent[ctx->save_sp_top]) {
                                BAIL("ARRAY with divergent stack (conditional elements)");
                        }
                        int saved = ctx->save_sp_stack[ctx->save_sp_top--];
                        int count = ctx->sp - saved;
                        int base_off = OP_OFF(saved);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, base_off);
                        jit_emit_mov(asm, BC_A2, BC_A1);
                        jit_emit_load_imm(asm, BC_A3, count);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_array);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp = saved + 1;
                        ctx->op_types[ctx->sp - 1] = ARRAY_TYPE;
                        DBG("ARRAY literal");
                        break;
                }

                CASE(ARRAY0) {
                        // Empty array
                        int off = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_array0);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(ARRAY_COMPR) {
                        i32 idx;
                        BC_READ(idx);

                        if (ctx->save_sp_divergent[ctx->save_sp_top]) {
                                BAIL("ARRAY_COMPR with divergent stack (conditional elements)");
                        }
                        int saved = ctx->save_sp_stack[ctx->save_sp_top--];
                        int count = ctx->sp - saved;

                        int off = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_A2, idx);
                        jit_emit_load_imm(asm, BC_A3, count);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_array_compr);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp = saved;
                        break;
                }

                CASE(DUP2_SWAP) {
                        // Before: ..., A, B (sp=N)
                        // After:  ..., A, B, B, A (sp=N+2)
                        // Copy B (at sp-1) to sp
                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_OPS, OP_OFF(ctx->sp - 1));
                        ctx->sp++;
                        // Copy A (now at sp-3) to sp
                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_OPS, OP_OFF(ctx->sp - 3));
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(LOAD_REF) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        bc_emit_deref(ctx, BC_S3, BC_LOC, n * VALUE_SIZE);
                        bc_push_from(ctx, BC_S3, 0);
                        break;
                }

                CASE(TARGET_REF) {
                        int n;
                        BC_READ(n);
                        int lbl_loop = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);
                        jit_emit_add_imm(asm, BC_S3, BC_LOC, n * VALUE_SIZE);
                        jit_emit_label(asm, lbl_loop);
                        jit_emit_ldrb(asm, BC_S0, BC_S3, VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_REF);
                        jit_emit_branch_ne(asm, lbl_done);
                        jit_emit_ldr64(asm, BC_S3, BC_S3, VAL_OFF_REF);
                        jit_emit_jump(asm, lbl_loop);
                        jit_emit_label(asm, lbl_done);
                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++;
                                // ASSIGN peeks, doesn't pop
                                bc_copy_value(ctx, BC_S3, 0, BC_OPS, OP_OFF(ctx->sp - 1));
                        } else if (ip < end && ((u8)*ip == INSTR_MUT_ADD || (u8)*ip == INSTR_MUT_SUB)) {
                                // TARGET_REF + MUT_ADD/MUT_SUB fusion (same as TARGET_LOCAL)
                                u8 mut_op = (u8)*ip++;
                                int addend_off = OP_OFF(ctx->sp - 1);

                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                jit_emit_ldrb(asm, BC_S0, BC_S3, VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_branch_ne(asm, lbl_slow);

                                jit_emit_ldrb(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_branch_ne(asm, lbl_slow);

                                jit_emit_ldr64(asm, BC_S0, BC_S3, VAL_OFF_Z);
                                jit_emit_ldr64(asm, BC_S1, BC_OPS, addend_off + VAL_OFF_Z);
                                if (mut_op == INSTR_MUT_ADD) {
                                        jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
                                } else {
                                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                                }
                                jit_emit_str64(asm, BC_S0, BC_S3, VAL_OFF_Z);
                                jit_emit_str64(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_Z);
                                jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_strb(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_TYPE);
                                jit_emit_jump(asm, lbl_done);

                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_mov(asm, BC_A1, BC_S3);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, addend_off);
                                jit_emit_mov(asm, BC_A3, BC_A2);
                                if (mut_op == INSTR_MUT_ADD) {
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_mut_add);
                                } else {
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_mut_sub);
                                }
                                jit_emit_call_reg(asm, BC_CALL);
                                jit_emit_label(asm, lbl_done);
                        } else {
                                // Deferred target for later MUT_ADD/SUB
                                ctx->tgt_kind = TGT_LOCAL;
                                ctx->tgt_index = n;
                        }
                        break;
                }

                CASE(MAYBE_ASSIGN)
                        // Conditional assign to target: if TOS is not nil/none, assign
                        // For simplicity, bail
                        BAIL("MAYBE_ASSIGN not yet supported");
                        break;

                CASE(CHECK_MATCH) {
                        // Pattern matching: stack has [value, pattern]
                        // Replace both with BOOLEAN result
                        dasm_State **asm = &ctx->asm;
                        int pat_off = OP_OFF(ctx->sp - 1);  // pattern (TOS)
                        int val_off = OP_OFF(ctx->sp - 2);  // value being matched
                        ctx->sp -= 2;
                        int res_off = OP_OFF(ctx->sp);

                        // Call jit_rt_check_match(ty, &result, &value, &pattern)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, res_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, val_off);
                        jit_emit_add_imm(asm, BC_A3, BC_OPS, pat_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_check_match);
                        jit_emit_call_reg(asm, BC_CALL);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        DBG("CHECK_MATCH");
                        break;
                }

                CASE(ASSIGN_SUBSCRIPT) {
                        // Stack: ..., value, container, subscript (TOS)
                        // After: ..., value (pops subscript + container, keeps value)
                        int sub_off = OP_OFF(ctx->sp - 1);
                        int con_off = OP_OFF(ctx->sp - 2);
                        int val_off = OP_OFF(ctx->sp - 3);

                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        // Fast path: container is array, subscript is non-negative int
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, con_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_ARRAY);
                        jit_emit_branch_ne(asm, lbl_slow);

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        // Load index
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_Z); // idx

                        // Load array pointer
                        jit_emit_ldr64(asm, BC_S1, BC_OPS, con_off + VAL_OFF_Z); // Array*

                        // Bounds check: 0 <= idx < array->count
                        jit_emit_ldr64(asm, BC_S2, BC_S1, 8);  // count (Array+8)

                        // idx < 0 => slow path (handles negative indices)
                        jit_emit_cmp_ri(asm, BC_S0, 0);
                        jit_emit_branch_lt(asm, lbl_slow);

                        // idx >= count => slow path
                        // cmp_lt sets BC_S2 = (idx < count), branch if NOT
                        jit_emit_cmp_lt(asm, BC_S2, BC_S0, BC_S2);
                        jit_emit_cbz(asm, BC_S2, lbl_slow);

                        // Compute item address: items + idx * 32
                        jit_emit_ldr64(asm, BC_S1, BC_S1, 0);  // items pointer
                        // BC_S0 = idx, shift left by 5 (multiply by 32)
                        jit_emit_load_imm(asm, BC_S2, 5);
                        jit_emit_shl(asm, BC_S0, BC_S0, BC_S2);
                        jit_emit_add(asm, BC_S1, BC_S1, BC_S0); // item_addr = items + idx*32

                        // Copy value (32 bytes) from ops[val_off] to item_addr
                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_OPS, val_off);
                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_S1, 0);
                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_OPS, val_off + 16);
                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_S1, 16);
                        jit_emit_jump(asm, lbl_done);

                        // Slow path: call helper
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, val_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, con_off);
                        jit_emit_add_imm(asm, BC_A3, BC_OPS, sub_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_assign_subscript);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_done);
                        ctx->sp -= 2; // pop subscript + container, keep value
                        break;
                }

                CASE(QUESTION) {
                        BAIL("QUESTION unsupported");
                        return false;
                }

                CASE(TAG) {
                        int tag;
                        BC_READ(tag);
                        // Push the tag value
                        // Tags are stored as VALUE_TAG with integer value
                        dasm_State **asm = &ctx->asm;
                        int off = OP_OFF(ctx->sp);

                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

                        jit_emit_load_imm(asm, BC_S0, VALUE_TAG);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

                        jit_emit_load_imm(asm, BC_S0, tag);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(CLASS) {
                        int cls;
                        BC_READ(cls);
                        dasm_State **asm = &ctx->asm;
                        int off = OP_OFF(ctx->sp);

                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

                        jit_emit_load_imm(asm, BC_S0, VALUE_CLASS);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

                        jit_emit_load_imm(asm, BC_S0, cls);
                        jit_emit_str32(asm, BC_S0, BC_OPS, off + VAL_OFF_CLASS);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(SUBSCRIPT) {
                        // Stack: ..., container, subscript (TOS) => result
                        int con_off = OP_OFF(ctx->sp - 2);
                        int sub_off = OP_OFF(ctx->sp - 1);
                        int res_off = con_off;

                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        Type *t0 = type_resolve_var(ctx->op_types[ctx->sp - 2]);
                        Class *c = expected_class_of(ctx->ty, t0);

                        bool try_array = (c != NULL && c->i == CLASS_ARRAY);
                        bool try_tuple = (c != NULL && c->i == CLASS_TUPLE);

                        int lbl_tuple = try_tuple ? bc_next_label(ctx) : lbl_slow;

                        // Fast path: Array.[](Int)
                        if (try_array) {
                                jit_emit_ldrb(asm, BC_S0, BC_OPS, con_off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_ARRAY);
                                jit_emit_branch_ne(asm, lbl_tuple);

                                jit_emit_ldrb(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_branch_ne(asm, lbl_slow);

                                // Load index and array pointer
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_Z); // idx
                                jit_emit_ldr64(asm, BC_S1, BC_OPS, con_off + VAL_OFF_Z); // Array*

                                // Bounds check
                                jit_emit_ldr64(asm, BC_S2, BC_S1, 8);  // count
                                jit_emit_cmp_ri(asm, BC_S0, 0);
                                jit_emit_branch_lt(asm, lbl_slow);
                                jit_emit_cmp_lt(asm, BC_S2, BC_S0, BC_S2); // BC_S2 = (idx < count)
                                jit_emit_cbz(asm, BC_S2, lbl_slow);

                                // Item address: items + idx * 32
                                jit_emit_ldr64(asm, BC_S1, BC_S1, 0);  // items
                                jit_emit_load_imm(asm, BC_S2, 5);
                                jit_emit_shl(asm, BC_S0, BC_S0, BC_S2);
                                jit_emit_add(asm, BC_S1, BC_S1, BC_S0); // &items[idx]

                                // Copy 32 bytes from items[idx] to ops[res_off]
                                // Can't use bc_copy_value (clobbers BC_S0/S1)
                                jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 0);
                                jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off);
                                jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 16);
                                jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off + 16);
                                jit_emit_jump(asm, lbl_done);
                        }

                        // Fast path: (T, ...).[](Int)
                        if (try_tuple) {
                                jit_emit_label(asm, lbl_tuple);

                                jit_emit_ldrb(asm, BC_S0, BC_OPS, con_off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_TUPLE);
                                jit_emit_branch_ne(asm, lbl_slow);

                                jit_emit_ldrb(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                jit_emit_branch_ne(asm, lbl_slow);

                                // Load index
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_Z); // idx

                                // Bounds check: 0 <= idx < count
                                jit_emit_ldr32(asm, BC_S2, BC_OPS, con_off + VAL_OFF_COUNT); // count
                                jit_emit_cmp_ri(asm, BC_S0, 0);
                                jit_emit_branch_lt(asm, lbl_slow);
                                jit_emit_cmp_lt(asm, BC_S2, BC_S0, BC_S2); // BC_S2 = (idx < count)
                                jit_emit_cbz(asm, BC_S2, lbl_slow);

                                // Compute item address: items + idx * 32
                                jit_emit_ldr64(asm, BC_S1, BC_OPS, con_off + VAL_OFF_ITEMS); // items
                                jit_emit_load_imm(asm, BC_S2, 5);
                                jit_emit_shl(asm, BC_S0, BC_S0, BC_S2);
                                jit_emit_add(asm, BC_S1, BC_S1, BC_S0); // &items[idx]

                                // Copy 32 bytes from items[idx] to ops[res_off]
                                jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 0);
                                jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off);
                                jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 16);
                                jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off + 16);
                                jit_emit_jump(asm, lbl_done);
                        }

                        // Slow path
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, res_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_subscript);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_done);
                        ctx->sp--;
                        break;
                }

                CASE(NONE_IF_NIL) {
                        // If TOS is nil, replace with NONE
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_not_nil = bc_next_label(ctx);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                        jit_emit_branch_ne(asm, lbl_not_nil);
                        // Is nil: set type to VALUE_NONE
                        jit_emit_load_imm(asm, BC_S0, VALUE_NONE);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_label(asm, lbl_not_nil);
                        break;
                }

                CASE(CHECK_INIT)
                        // Runtime check that object is initialized --- skip in JIT
                        break;

                CASE(THROW_IF_NIL) {
                        // If TOS is nil, tag with MatchError and throw
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_not_nil = bc_next_label(ctx);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                        jit_emit_branch_ne(asm, lbl_not_nil);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_bad_match);
                        jit_emit_call_reg(asm, BC_CALL);
                        jit_emit_label(asm, lbl_not_nil);
                        break;
                }

                CASE(THROW) {
                        // TOS is the exception value --- call vm_throw(ty, &exc)
                        int exc_off = OP_OFF(ctx->sp - 1);
                        ctx->sp--;
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, exc_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_throw);
                        jit_emit_call_reg(asm, BC_CALL);
                        // vm_throw never returns
                        ctx->dead = true;
                        break;
                }

                CASE(BAD_CALL)
                        BC_SKIPSTR();
                        BC_SKIPSTR();
                        // This is an error path --- should not be reached at runtime
                        break;

                CASE(BAD_MATCH)
                        int tos_off = OP_OFF(ctx->sp - 1);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_bad_match);
                        jit_emit_call_reg(asm, BC_CALL);
                        break;

                CASE(BAD_DISPATCH)
                        break;

                CASE(BAD_ASSIGN)
                        BC_SKIPSTR();
                        break;

                CASE(BIT_AND)
                        bc_emit_arith(ctx, (void *)jit_rt_bit_and);
                        break;

                CASE(BIT_OR)
                        bc_emit_arith(ctx, (void *)jit_rt_bit_or);
                        break;

                CASE(BIT_XOR)
                        bc_emit_arith(ctx, (void *)jit_rt_bit_xor);
                        break;

                CASE(SHL)
                        bc_emit_arith(ctx, (void *)jit_rt_shl);
                        break;

                CASE(SHR)
                        bc_emit_arith(ctx, (void *)jit_rt_shr);
                        break;

                CASE(INC) {
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        // Fast path: if int, add 1 to z
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_add_imm(asm, BC_S0, BC_S0, 1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_jump(asm, lbl_done);

                        // Slow path: call IncValue(ty, &ops[sp-1])
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_inc);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(DEC) {
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_load_imm(asm, BC_S1, 1);
                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_jump(asm, lbl_done);

                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_dec);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(STRING) {
                        int n;
                        BC_READ(n);
                        // jit_rt_string(ty, &ops[sp], n)
                        int off = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_string);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        ctx->op_types[ctx->sp - 1] = STRING_TYPE;
                        break;
                }

                CASE(REAL) {
                        double x;
                        BC_READ(x);
                        int off = OP_OFF(ctx->sp);

                        // Zero the slot
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

                        // Set type = VALUE_REAL
                        jit_emit_load_imm(asm, BC_S0, VALUE_REAL);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

                        // Set real value (copy double bits into z field)
                        {
                                union { double d; intmax_t z; } u;
                                u.d = x;
                                jit_emit_load_imm(asm, BC_S0, u.z);
                        }
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        ctx->op_types[ctx->sp - 1] = TYPE_FLOAT;
                        break;
                }

                CASE(SLICE)
                        bc_emit_call_method(ctx, code + off, NAMES.slice, 3, -1);
                        break;

                CASE(CMP)
                        bc_emit_binop_helper(ctx, (void *)jit_rt_cmp);
                        break;

                CASE(COUNT)
                        bc_emit_unop_helper(ctx, (void *)jit_rt_count);
                        ctx->op_types[ctx->sp - 1] = INT_TYPE;
                        break;

                CASE(GET_TAG) {
                        // Pop value, push its tag (or nil if no tag)
                        // For now, use a helper
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_has_tag = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);

                        // Check tags field
                        jit_emit_ldr32(asm, BC_S0, BC_OPS, off + VAL_OFF_TAGS);
                        jit_emit_cbnz(asm, BC_S0, lbl_has_tag);

                        // No tag: write NIL
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_NIL);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_jump(asm, lbl_done);

                        // Has tag: call tags_first(ty, tags) and make TAG value
                        jit_emit_label(asm, lbl_has_tag);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_ldr32(asm, BC_A1, BC_OPS, off + VAL_OFF_TAGS);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)tags_first);
                        jit_emit_call_reg(asm, BC_CALL);
                        // Result in w0 (tag id)
                        jit_emit_mov(asm, BC_S1, BC_RET); // save tag id
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_TAG);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_str64(asm, BC_S1, BC_OPS, off + VAL_OFF_Z);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(MATCH_TAG) {
                        u8 wrapped = (u8)*ip++;
                        i32 num_entries;
                        BC_READ(num_entries);
                        i32 fail_off;
                        BC_READ(fail_off);
                        int fail_target = (int)(ip - code) + fail_off;
                        int fail_lbl = bc_label_for(ctx, fail_target);

                        int off = OP_OFF(ctx->sp - 1);

                        if (wrapped) {
                                // Check value has tags (type & VALUE_TAGGED)
                                jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                                jit_emit_load_imm(asm, BC_S1, VALUE_TAGGED);
                                jit_emit_and(asm, BC_S0, BC_S0, BC_S1);
                                jit_emit_cbz(asm, BC_S0, fail_lbl);
                                // Get tag id: tags_first(ty, top->tags)
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_ldr32(asm, BC_A1, BC_OPS, off + VAL_OFF_TAGS);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)tags_first);
                                jit_emit_call_reg(asm, BC_CALL);
                                // Result tag id in w0
                                jit_emit_mov(asm, BC_S0, BC_RET);
                        } else {
                                // Check type == VALUE_TAG
                                jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_TAG);
                                jit_emit_branch_ne(asm, fail_lbl);
                                // Load tag id from z field
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        }

                        // Now BC_S0 = subject tag id
                        // Emit comparisons for each entry
                        for (i32 q = 0; q < num_entries; ++q) {
                                i32 entry_id;
                                BC_READ(entry_id);
                                i32 jmp_off;
                                BC_READ(jmp_off);
                                int jmp_target = (int)(ip - code) + jmp_off;
                                int jmp_lbl = bc_label_for(ctx, jmp_target);

                                jit_emit_cmp_ri(asm, BC_S0, entry_id);
                                jit_emit_branch_eq(asm, jmp_lbl);
                        }

                        // No match: fall through to fail
                        jit_emit_jump(asm, fail_lbl);
                        // sp unchanged (MATCH_TAG doesn't pop)
                        break;
                }

                CASE(UNARY_OP) {
                        int n;
                        BC_READ(n);
                        // Call DoUnaryOp(ty, n, false) --- but it operates on VM stack.
                        // For now bail.
                        BAIL("UNARY_OP unsupported");
                        return false;
                }

                CASE(BINARY_OP) {
                        int n;
                        BC_READ(n);
                        BAIL("BINARY_OP unsupported");
                        return false;
                }

                CASE(JUMP_WTF) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid JUMP_WTF target");

                        int tos_off = OP_OFF(ctx->sp - 1);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, tos_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);

                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_ne(asm, lbl_target);

                        ctx->sp--;
                        break;
                }

                CASE(TO_STRING) {
                        // Convert TOS to string in-place
                        int top_off = OP_OFF(ctx->sp - 1);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, top_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_to_string);
                        jit_emit_call_reg(asm, BC_CALL);
                        break;
                }

                CASE(CONCAT_STRINGS) {
                        int n;
                        BC_READ(n);
                        int base_off = OP_OFF(ctx->sp - n);
                        ctx->sp -= n;
                        int res_off = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, res_off); // result
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, base_off); // base
                        jit_emit_load_imm(asm, BC_A3, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_concat_strings);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(RANGE)
                CASE(INCRANGE) {
                        // Stack: ..., start, end => result
                        int a_off = OP_OFF(ctx->sp - 2);
                        int b_off = OP_OFF(ctx->sp - 1);
                        ctx->sp -= 2;
                        int res_off = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, res_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, a_off);
                        jit_emit_add_imm(asm, BC_A3, BC_OPS, b_off);
                        jit_emit_load_imm(asm, BC_CALL,
                                (iptr)(op == INSTR_RANGE ? jit_rt_range : jit_rt_incrange));
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(ASSIGN_GLOBAL) {
                        int n;
                        BC_READ(n);
                        // Stack: ..., value (TOS) => pops value
                        int val_off = OP_OFF(ctx->sp - 1);
                        ctx->sp--;
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_A1, n);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, val_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_assign_global);
                        jit_emit_call_reg(asm, BC_CALL);
                        break;
                }

                CASE(TARGET_GLOBAL) {
                        int n;
                        BC_READ(n);
                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++; // consume ASSIGN
                                // globals[n] = peek TOS
                                int val_off = OP_OFF(ctx->sp - 1);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_load_imm(asm, BC_A1, n);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, val_off);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_assign_global);
                                jit_emit_call_reg(asm, BC_CALL);
                        } else {
                                BAIL("TARGET_GLOBAL without ASSIGN fusion");
                                return false;
                        }
                        break;
                }

                CASE(TARGET_CAPTURED) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++; // consume ASSIGN
                                // *env[n] = peek TOS
                                int val_off = OP_OFF(ctx->sp - 1);
                                // Load env[n] pointer
                                jit_emit_ldr64(asm, BC_S2, BC_ENV, n * 8);
                                // Copy value to *env[n]
                                bc_copy_value(ctx, BC_S2, 0, BC_OPS, val_off);
                        } else if (ip < end && ((u8)*ip == INSTR_MUT_ADD || (u8)*ip == INSTR_MUT_SUB)) {
                                // TARGET_CAPTURED + MUT_ADD/MUT_SUB fusion
                                u8 mut_op = (u8)*ip++;
                                int addend_off = OP_OFF(ctx->sp - 1);
                                // Load env[n] pointer => BC_S2
                                jit_emit_ldr64(asm, BC_S2, BC_ENV, n * 8);
                                // Call runtime: jit_rt_mut_add/sub(ty, target=*env[n], addend, result)
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_mov(asm, BC_A1, BC_S2);                            // target = env[n]
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, addend_off);           // addend
                                jit_emit_mov(asm, BC_A3, BC_A2);                                // result = addend slot
                                if (mut_op == INSTR_MUT_ADD) {
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_mut_add);
                                } else {
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_mut_sub);
                                }
                                jit_emit_call_reg(asm, BC_CALL);
                                // sp unchanged
                        } else {
                                // Load env[n] pointer => BC_S2
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_ldr64(asm, BC_A1, BC_ENV, n * 8);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_push_target);
                                jit_emit_call_reg(asm, BC_CALL);
                        }
                        break;
                }

                CASE(TUPLE) {
                        i32 n;
                        BC_READ(n);

                        uptr ids;
                        BC_READ(ids);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_A3, (iptr)ids);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_tuple);
                        jit_emit_call_reg(asm, BC_CALL);

                        ctx->sp = ctx->sp - n + 1;
                        break;
                }

                CASE(JUMP_IF_TYPE) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid JUMP_IF_TYPE target");

                        int type_val;
                        BC_READ(type_val);

                        int tos_off = OP_OFF(ctx->sp - 1);

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, tos_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, type_val);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, lbl_target);
                        break;
                }

                CASE(ENSURE_LEN_TUPLE) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid ENSURE_LEN_TUPLE target");

                        int expected_count;
                        BC_READ(expected_count);

                        int tos_off = OP_OFF(ctx->sp - 1);

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, tos_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_TUPLE);
                        jit_emit_branch_ne(asm, fail_lbl);

                        jit_emit_ldr32(asm, BC_S0, BC_OPS, tos_off + VAL_OFF_COUNT);
                        jit_emit_cmp_ri(asm, BC_S0, expected_count);
                        jit_emit_branch_gt(asm, fail_lbl);
                        break;
                }

                CASE(TRY_TAG_POP) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid TRY_TAG_POP target");

                        int tag;
                        BC_READ(tag);

                        int val_off = OP_OFF(ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, val_off);
                        jit_emit_load_imm(asm, BC_A2, tag);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_tag_pop);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);
                        break;
                }

                CASE(RENDER_TEMPLATE) {
                        uptr expr_ptr;
                        BC_READ(expr_ptr);
                        int dst = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, dst);
                        jit_emit_load_imm(asm, BC_A2, (iptr)expr_ptr);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_render_template);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(PUSH_TUPLE_ELEM) {
                        i32 idx;
                        BC_READ(idx);
                        int lbl_fail = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp - 1) + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_TUPLE);
                        jit_emit_branch_ne(asm, lbl_fail);
                        jit_emit_ldr32(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp - 1) + VAL_OFF_COUNT);
                        jit_emit_cmp_ri(asm, BC_S0, idx);
                        jit_emit_branch_le(asm, lbl_fail);
                        jit_emit_ldr64(asm, BC_S3, BC_OPS, OP_OFF(ctx->sp - 1) + VAL_OFF_ITEMS);
                        bc_push_from(ctx, BC_S3, idx * sizeof (Value));
                        jit_emit_jump(asm, lbl_done);
                        jit_emit_label(asm, lbl_fail);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp - 1));
                        jit_emit_load_imm(asm, BC_A2, (iptr)(code + off));
                        jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_fail);
                        jit_emit_call_reg(asm, BC_CALL);
                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(INDEX_TUPLE) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid INDEX_TUPLE target");

                        int idx;
                        BC_READ(idx);

                        int tos_off = OP_OFF(ctx->sp - 1);
                        int dst_off = OP_OFF(ctx->sp);

                        jit_emit_add_imm(asm, BC_A0, BC_OPS, tos_off);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, dst_off);
                        jit_emit_load_imm(asm, BC_A2, idx);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_index_tuple);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(TRY_TUPLE_MEMBER) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid TRY_TUPLE_MEMBER target");

                        u8 required;
                        BC_READ(required);
                        int name_id;
                        BC_READ(name_id);

                        int tos_off = OP_OFF(ctx->sp - 1);
                        int dst_off = OP_OFF(ctx->sp);

                        jit_emit_add_imm(asm, BC_A0, BC_OPS, tos_off);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, dst_off);
                        jit_emit_load_imm(asm, BC_A2, required);
                        jit_emit_load_imm(asm, BC_A3, name_id);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_tuple_member);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(TRY_STEAL_TAG) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid TRY_STEAL_TAG target");

                        int tos_off = OP_OFF(ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_pop_target);
                        jit_emit_call_reg(asm, BC_CALL);
                        jit_emit_mov(asm, BC_A2, BC_RET);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_steal_tag);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);
                        break;
                }

                CASE(JII) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int target_lbl = bc_find_label(ctx, target);
                        if (target_lbl < 0) BAIL("invalid JII target");

                        int class_id;
                        BC_READ(class_id);

                        bool pop_val = (class_id < 0);
                        int actual_class = pop_val ? -class_id : class_id;

                        int val_off = OP_OFF(ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, val_off);
                        jit_emit_load_imm(asm, BC_A2, actual_class);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_jii);
                        jit_emit_call_reg(asm, BC_CALL);

                        if (pop_val) {
                                ctx->sp--;
                        }

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_ne(asm, target_lbl);
                        break;
                }

                CASE(BIND_INSTANCE) {
                        int n;
                        int z;
                        BC_READ(n);
                        BC_READ(z);

                        int tos_off = OP_OFF(ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_A3, z);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_bind_instance);
                        jit_emit_call_reg(asm, BC_CALL);
                        break;
                }

                CASE(ENSURE_EQUALS_VAR) {
                        int jump_off;
                        BC_READ(jump_off);
                        int bc_target = (int)(ip - code) + jump_off;
                        int target_lbl = bc_label_for(ctx, bc_target);

                        int val_off = OP_OFF(ctx->sp - 1);
                        int tos_off = OP_OFF(ctx->sp - 2);
                        ctx->sp--;

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, val_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_ensure_equals_var);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, bc_target, ctx->sp);
                        jit_emit_branch_eq(asm, target_lbl);
                        break;
                }

                CASE(TRY_INDEX) {
                        int jump_off;
                        BC_READ(jump_off);
                        int bc_target = (int)(ip - code) + jump_off;
                        int target_lbl = bc_label_for(ctx, bc_target);

                        int idx;
                        BC_READ(idx);
                        u8 required;
                        BC_READ(required);

                        int tos_off = OP_OFF(ctx->sp - 1);
                        int dst_off = OP_OFF(ctx->sp);

                        jit_emit_add_imm(asm, BC_A0, BC_OPS, tos_off);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, dst_off);
                        jit_emit_load_imm(asm, BC_A2, idx);
                        jit_emit_load_imm(asm, BC_A3, required);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_index);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, bc_target, ctx->sp);
                        jit_emit_branch_eq(asm, target_lbl);

                        ctx->sp++;
                        break;
                }

                CASE(JNI) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int target_lbl = bc_find_label(ctx, target);
                        if (target_lbl < 0) BAIL("invalid JNI target");

                        int class_id;
                        BC_READ(class_id);

                        bool pop_val = (class_id < 0);
                        int actual_class = pop_val ? -class_id : class_id;

                        int val_off = OP_OFF(ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, val_off);
                        jit_emit_load_imm(asm, BC_A2, actual_class);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_jii);
                        jit_emit_call_reg(asm, BC_CALL);

                        if (pop_val) {
                                ctx->sp--;
                        }

                        // JNI: jump if NOT instance (opposite of JII)
                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, target_lbl);
                        break;
                }

                CASE(ENSURE_LEN) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid ENSURE_LEN target");

                        int expected_len;
                        BC_READ(expected_len);

                        int tos_off = OP_OFF(ctx->sp - 1);

                        // Check type == VALUE_ARRAY
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, tos_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_ARRAY);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_ne(asm, fail_lbl);

                        // Load array pointer (at union offset = VAL_OFF_Z)
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, tos_off + VAL_OFF_Z);
                        // Load array->count (offsetof(Array, count))
                        jit_emit_ldr64(asm, BC_S0, BC_S0, (int)offsetof(Array, count));
                        // If count > expected_len, jump to fail
                        jit_emit_cmp_ri(asm, BC_S0, expected_len);
                        jit_emit_branch_gt(asm, fail_lbl);
                        break;
                }

                CASE(CLEAR_RC) {
                        // ty->st.rc = 0;
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_str32(asm, BC_S0, BC_TY, (int)offsetof(Ty, st.rc));
                        break;
                }

                CASE(GET_NEXT) {
                        BAIL("GET_NEXT not supported (use LOOP_ITER/LOOP_CHECK)");
                        return false;
                }

                CASE(LOOP_ITER) {
                        // Call runtime helper: push SENTINEL, RC=0, IterGetNext
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_loop_iter);
                        jit_emit_call_reg(asm, BC_CALL);
                        // Compiler tracks LOOP_ITER as sp += 2 (SENTINEL + one result)
                        ctx->sp += 2;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(LOOP_CHECK) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int exit_lbl = bc_find_label(ctx, target);
                        if (exit_lbl < 0) BAIL("invalid LOOP_CHECK target");

                        int var_count;
                        BC_READ(var_count);

                        // Call runtime helper: returns true if loop done (NONE)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_A1, var_count);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp - 1));
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_loop_check);
                        jit_emit_call_reg(asm, BC_CALL);

                        // Exit path: helper popped 4 values
                        bc_set_label_sp(ctx, target, ctx->sp - 4);

                        // Check return value: true = exit loop
                        jit_emit_cmp_ri32(asm, BC_RET, 0);
                        jit_emit_branch_ne(asm, exit_lbl);

                        // Continue path: stack adjusted to have var_count values
                        // Net change from LOOP_CHECK: +(var_count - 1) relative to LOOP_ITER
                        ctx->sp += (var_count - 1);
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(DICT) {
                        if (ctx->save_sp_top < 0) {
                                if (ctx->dead) break;
                                BAIL("DICT stack underflow");
                        }
                        int saved = ctx->save_sp_stack[ctx->save_sp_top--];
                        int count = ctx->sp - saved;
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A2, count);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_dict);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp = saved + 1;
                        break;
                }

                CASE(DEFAULT_DICT) {
                        if (ctx->save_sp_top < 0) {
                                if (ctx->dead) break;
                                BAIL("DEFAULT_DICT stack underflow");
                        }
                        int saved = ctx->save_sp_stack[ctx->save_sp_top--];
                        int count = ctx->sp - 1 - saved;
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A2, count);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_default_dict);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp = saved + 1;
                        break;
                }

                CASE(CALL_STATIC_METHOD) {
                        int class_id, argc, method_id, nkw;
                        BC_READ(class_id);
                        BC_READ(argc);
                        BC_READ(method_id);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (nkw > 0 || argc == -1) {
                                BAIL("CALL_STATIC_METHOD with kwargs/spread not supported");
                        }

                        // Args are on the operand stack: ops[sp-argc..sp-1]
                        // Result replaces the args: goes at ops[sp - argc]
                        int result_off = OP_OFF(ctx->sp - argc);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                        jit_emit_load_imm(asm, BC_A2, class_id);
                        jit_emit_load_imm(asm, BC_A3, argc);
                        jit_emit_load_imm(asm, BC_A4, method_id);
                        jit_emit_load_imm(asm, BC_A5, nkw);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_static_method);
                        jit_emit_call_reg(asm, BC_CALL);

                        // argc args consumed, 1 result produced
                        ctx->sp -= (argc - 1);
                        break;
                }

                CASE(MUT_ADD)
                CASE(MUT_SUB)
                CASE(MUT_MUL)
                CASE(MUT_DIV)
                CASE(MUT_MOD)
                CASE(MUT_OR)
                CASE(MUT_AND)
                CASE(MUT_XOR)
                CASE(MUT_SHL)
                CASE(MUT_SHR) {
                        if (ctx->tgt_kind == TGT_NONE) {
                                BAIL("JIT: MUT_ADD/MUT_SUB without target");
                        }

                        int addend_off = OP_OFF(ctx->sp - 1);

                        if (ctx->tgt_kind == TGT_LOCAL) {
                                int local_off = ctx->tgt_index * VALUE_SIZE;
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                if (op == INSTR_MUT_ADD || op == INSTR_MUT_SUB) {
                                        // Fast path: check both are VALUE_INTEGER
                                        jit_emit_ldrb(asm, BC_S0, BC_LOC, local_off + VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        jit_emit_ldrb(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        // Both integers: load, add/sub, store to local and ops
                                        jit_emit_ldr64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);
                                        jit_emit_ldr64(asm, BC_S1, BC_OPS, addend_off + VAL_OFF_Z);
                                        if (op == INSTR_MUT_ADD) {
                                                jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
                                        } else {
                                                jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                                        }
                                        jit_emit_str64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);
                                        jit_emit_str64(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_Z);
                                        jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_strb(asm, BC_S0, BC_OPS, addend_off + VAL_OFF_TYPE);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                // Slow path (always taken for MUL/DIV/MOD)
                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, local_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, addend_off);
                                jit_emit_mov(asm, BC_A3, BC_A2);
                                iptr local_helper =
                                        op == INSTR_MUT_ADD ? (iptr)jit_rt_mut_add :
                                        op == INSTR_MUT_SUB ? (iptr)jit_rt_mut_sub :
                                        op == INSTR_MUT_MUL ? (iptr)jit_rt_mut_mul :
                                        op == INSTR_MUT_DIV ? (iptr)jit_rt_mut_div :
                                        op == INSTR_MUT_MOD ? (iptr)jit_rt_mut_mod :
                                        op == INSTR_MUT_OR  ? (iptr)jit_rt_mut_or :
                                        op == INSTR_MUT_AND ? (iptr)jit_rt_mut_and :
                                        op == INSTR_MUT_XOR ? (iptr)jit_rt_mut_xor :
                                        op == INSTR_MUT_SHL ? (iptr)jit_rt_mut_shl :
                                                              (iptr)jit_rt_mut_shr;
                                jit_emit_load_imm(asm, BC_CALL, local_helper);
                                jit_emit_call_reg(asm, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_CAPTURED) {
                                // Load env[n] => BC_S2, then call helper
                                jit_emit_ldr64(asm, BC_S2, BC_ENV, ctx->tgt_index * 8);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_mov(asm, BC_A1, BC_S2);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, addend_off);
                                jit_emit_mov(asm, BC_A3, BC_A2);
                                iptr cap_helper =
                                        op == INSTR_MUT_ADD ? (iptr)jit_rt_mut_add :
                                        op == INSTR_MUT_SUB ? (iptr)jit_rt_mut_sub :
                                        op == INSTR_MUT_MUL ? (iptr)jit_rt_mut_mul :
                                        op == INSTR_MUT_DIV ? (iptr)jit_rt_mut_div :
                                        op == INSTR_MUT_MOD ? (iptr)jit_rt_mut_mod :
                                        op == INSTR_MUT_OR  ? (iptr)jit_rt_mut_or :
                                        op == INSTR_MUT_AND ? (iptr)jit_rt_mut_and :
                                        op == INSTR_MUT_XOR ? (iptr)jit_rt_mut_xor :
                                        op == INSTR_MUT_SHL ? (iptr)jit_rt_mut_shl :
                                                              (iptr)jit_rt_mut_shr;
                                jit_emit_load_imm(asm, BC_CALL, cap_helper);
                                jit_emit_call_reg(asm, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_MEMBER) {
                                // TARGET_MEMBER + MUT op
                                if (op == INSTR_MUT_OR || op == INSTR_MUT_AND || op == INSTR_MUT_XOR
                                    || op == INSTR_MUT_SHL || op == INSTR_MUT_SHR) {
                                        BAIL("JIT: MUT bitwise on member not yet supported");
                                }
                                int obj_off = OP_OFF(ctx->tgt_obj_sp);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);       // obj
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);       // member_id
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, addend_off);    // addend
                                jit_emit_add_imm(asm, BC_A4, BC_OPS, addend_off);    // result = addend slot
                                iptr mem_helper =
                                        op == INSTR_MUT_ADD ? (iptr)jit_rt_member_mut_add :
                                        op == INSTR_MUT_SUB ? (iptr)jit_rt_member_mut_sub :
                                        op == INSTR_MUT_MUL ? (iptr)jit_rt_member_mut_mul :
                                        op == INSTR_MUT_DIV ? (iptr)jit_rt_member_mut_div :
                                                              (iptr)jit_rt_member_mut_mod;
                                jit_emit_load_imm(asm, BC_CALL, mem_helper);
                                jit_emit_call_reg(asm, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SELF_MEMBER) {
                                // TARGET_SELF_MEMBER + MUT op
                                if (op == INSTR_MUT_OR || op == INSTR_MUT_AND || op == INSTR_MUT_XOR
                                    || op == INSTR_MUT_SHL || op == INSTR_MUT_SHR) {
                                        BAIL("JIT: MUT bitwise on self member not yet supported");
                                }
                                int self_off = ctx->param_count * VALUE_SIZE;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, self_off);      // obj = self
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);       // member_id
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, addend_off);    // addend
                                jit_emit_add_imm(asm, BC_A4, BC_OPS, addend_off);    // result = addend slot
                                iptr self_helper =
                                        op == INSTR_MUT_ADD ? (iptr)jit_rt_member_mut_add :
                                        op == INSTR_MUT_SUB ? (iptr)jit_rt_member_mut_sub :
                                        op == INSTR_MUT_MUL ? (iptr)jit_rt_member_mut_mul :
                                        op == INSTR_MUT_DIV ? (iptr)jit_rt_member_mut_div :
                                                              (iptr)jit_rt_member_mut_mod;
                                jit_emit_load_imm(asm, BC_CALL, self_helper);
                                jit_emit_call_reg(asm, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SUBSCRIPT) {
                                // TARGET_SUBSCRIPT + MUT op
                                if (op == INSTR_MUT_OR || op == INSTR_MUT_AND || op == INSTR_MUT_XOR
                                    || op == INSTR_MUT_SHL || op == INSTR_MUT_SHR) {
                                        BAIL("JIT: MUT bitwise on subscript not yet supported");
                                }
                                // val=addend at sp-1, container at tgt_obj_sp, subscript at tgt_index
                                int container_off = OP_OFF(ctx->tgt_obj_sp);
                                int subscript_off = OP_OFF(ctx->tgt_index);
                                // jit_rt_subscript_mut_*(ty, val, container, subscript)
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, addend_off);      // val
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, container_off);   // container
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, subscript_off);   // subscript
                                iptr sub_helper =
                                        op == INSTR_MUT_ADD ? (iptr)jit_rt_subscript_mut_add :
                                        op == INSTR_MUT_SUB ? (iptr)jit_rt_subscript_mut_sub :
                                        op == INSTR_MUT_MUL ? (iptr)jit_rt_subscript_mut_mul :
                                        op == INSTR_MUT_DIV ? (iptr)jit_rt_subscript_mut_div :
                                                              (iptr)jit_rt_subscript_mut_mod;
                                jit_emit_load_imm(asm, BC_CALL, sub_helper);
                                jit_emit_call_reg(asm, BC_CALL);
                        }

                        ctx->tgt_kind = TGT_NONE;
                        // sp unchanged: addend replaced by result
                        break;
                }

                CASE(PUSH_INDEX) {
                        int n;
                        BC_READ(n);
                        int dst = OP_OFF(ctx->sp);
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 8);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 16);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst + 24);
                        jit_emit_load_imm(asm, BC_S0, VALUE_INDEX);
                        jit_emit_strb(asm, BC_S0, BC_OPS, dst + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, n);
                        jit_emit_str32(asm, BC_S0, BC_OPS, dst + offsetof(Value, nt));
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }


                CASE(CAPTURE) {
                        int local_idx;
                        BC_READ(local_idx);
                        int env_idx;
                        BC_READ(env_idx);

                        // => capture(ty, &locals[local_idx], env, env_idx)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_LOC, local_idx * VALUE_SIZE);
                        jit_emit_mov(asm, BC_A2, BC_ENV);
                        jit_emit_load_imm(asm, BC_A3, env_idx);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_capture);
                        jit_emit_call_reg(asm, BC_CALL);
                        break;
                }

                CASE(FUNCTION) {
                        int bound_caps;
                        BC_READ(bound_caps);

                        // Save the current IP position (before alignment)
                        // The runtime helper will align and parse the function info
                        char const *fn_ip = ip;

                        // Align and skip the function body in our bytecode scan
                        ip = ALIGNED_FOR(i64, ip);
                        i32 const *fn_info = (i32 const *)ip;
                        int hs   = fn_info[FUN_INFO_HEADER_SIZE];
                        int size = fn_info[FUN_INFO_CODE_SIZE];
                        int nEnv = fn_info[FUN_INFO_CAPTURES];
                        int ncaps = (bound_caps > 0) ? nEnv - bound_caps : nEnv;
                        ip += hs + size;

                        // Skip capture pairs
                        for (int q = 0; q < ncaps; ++q) {
                                ip += sizeof (bool);
                                ip += sizeof (int);
                        }

                        // Emit: call jit_rt_function(ty, &ops[sp], fn_ip, bound_caps) => returns new ip
                        int dst = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, dst);
                        jit_emit_load_imm(asm, BC_A2, (iptr)fn_ip);
                        jit_emit_load_imm(asm, BC_A3, bound_caps);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_function);
                        jit_emit_call_reg(asm, BC_CALL);
                        // Return value (new ip) is in x0 but we don't need it ---
                        // we already advanced ip statically

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;

                        DBG("FUNCTION");
                        break;
                }

                CASE(CLASS_OF)
                        BAIL("CLASS_OF unsupported");
                        return false;

                default:
                        LOG("JIT: unknown emit opcode %d=%s", op, GetInstructionName(op));
                        return false;
                }
        }

        return true;

#undef BC_READ
#undef BC_SKIP
#undef BC_SKIPSTR
}

// ============================================================================
// Bytecode JIT: main entry point
// ============================================================================

JitInfo *
jit_compile(Ty *ty, Value const *func)
{
#ifdef TY_PROFILER
        u64 compile_t0 = jit_wall_time();
#endif

        i32 const *info = func->info;
        int code_size   = info[FUN_INFO_CODE_SIZE];
        int bound       = info[FUN_INFO_BOUND];
        int param_count = info[FUN_INFO_PARAM_COUNT];
        char const *bc  = (char const *)info + info[FUN_INFO_HEADER_SIZE];

        char const *name = name_of(func);

        Expr const *_e = !from_eval(func) ? expr_of(func) : NULL;
        char const *clsn = (_e && _e->class) ? _e->class->name : "";

#if JIT_SCAN_LOG
        LOGX("JIT: compiling %s%s%s (params=%d, bound=%d, code_size=%d, caps=%d)",
            name, clsn[0] ? " of " : "", clsn,
            param_count, bound, code_size, info[FUN_INFO_CAPTURES]);
#endif

#if JIT_DUMP_DIS
        static _Thread_local byte_vector dis;
        DumpProgram(ty, &dis, "<bytecode>", code_of(func), code_of(func) + code_size_of(func), false);
        xvP(dis, '\0');
        LOGX("JIT: bytecode for %s:\n%s", name, vv(dis));
        v0(dis);
#endif

        JitCtx ctx = {
                .ty             = ty,
                .func           = func,
                .param_count    = param_count,
                .bound          = bound,
                .name           = name,
                .sp             = 0,
                .max_sp         = 0,
                .next_label     = 0,
                .label_capacity = MAX_BC_LABELS,
                .label_count    = 0,
                .save_sp_top    = -1,
                .self_class_id  = -1,
        };

        Expr const *expr = expr_of(func);
        if (expr != NULL) {
                ctx.func_type = expr->_type;
                if (expr->class != NULL) {
                        ctx.self_class = expr->class;
                        ctx.self_class_id = expr->class->i;
                }
        }

        // Pre-scan: discover jump targets, check support
        if (!bc_prescan(&ctx, bc, code_size)) {
#if JIT_SCAN_LOG
                LOGX("JIT: bail on %s", name);
#endif
                return NULL;
        }

        // Allocate a special label for the return epilogue
        bc_label_for(&ctx, -1);

        // Set up DynASM
        dasm_State *asm;
        dasm_init(&asm, DASM_MAXSECTION);

        void *global_labels[JIT_GLOB__MAX];
        dasm_setupglobal(&asm, global_labels, JIT_GLOB__MAX);
        dasm_growpc(&asm, MAX_BC_LABELS);
        dasm_setup(&asm, jit_actions);

        jit_emit_prologue(&asm, bound);

        ctx.asm = asm; // sync after DynASM setup

        // Trampoline support: check if we're resuming after a sub-call.
        // Load ty->jit.resume_idx; if non-zero, jump to a dispatch block
        // that redirects to the appropriate resume label.
        int lbl_dispatch = bc_next_label(&ctx);
        int lbl_normal_start = bc_next_label(&ctx);
        ctx.call_site_count = 0;

        asm = ctx.asm; // sync: bc_next_label may have grown pclabels

        jit_emit_ldr32(&asm, BC_S0, BC_TY, OFF_JIT_RESUME);
        jit_emit_cbnz(&asm, BC_S0, lbl_dispatch);
        jit_emit_label(&asm, lbl_normal_start);

        // Emit bytecode
        ctx.asm = asm;
        if (!bc_emit(&ctx, bc, code_size)) {
                LOG("JIT: emission failed for %s", name);
                dasm_free(&asm);
                return NULL;
        }
        asm = ctx.asm; // refresh: bc_emit may have grown pclabels

        // Emit return epilogue at the special label
        int lbl_ret = bc_find_label(&ctx, -1);
        if (lbl_ret >= 0) {
                jit_emit_label(&asm, lbl_ret);
        }

        jit_emit_epilogue(&asm);

        // Emit the resume dispatch block.
        // This is reached when jit.resume_idx != 0 (checked at function entry).
        // BC_S0 still holds the resume_idx value loaded before the cbnz.
        if (ctx.call_site_count > 0) {
                jit_emit_label(&asm, lbl_dispatch);
                for (int i = 0; i < ctx.call_site_count; ++i) {
                        jit_emit_cmp_ri(&asm, BC_S0, i + 1);
                        jit_emit_branch_eq(&asm, ctx.resume_labels[i]);
                }
                // Fallback: should never happen, but jump to normal start
                jit_emit_jump(&asm, lbl_normal_start);
        } else {
                // No call sites — dispatch label still needs to exist
                jit_emit_label(&asm, lbl_dispatch);
                jit_emit_jump(&asm, lbl_normal_start);
        }

        // Link and encode
        usize final_size;
        int status = dasm_link(&asm, &final_size);
        if (status != DASM_S_OK) {
                dasm_free(&asm);
                return NULL;
        }

        void *code = mmap(
                NULL, final_size,
                PROT_READ | PROT_WRITE,
#ifdef MAP_JIT
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT,
#else
                MAP_PRIVATE | MAP_ANONYMOUS,
#endif
                -1, 0
        );

        if (code == MAP_FAILED) {
                dasm_free(&asm);
                return NULL;
        }

        dasm_encode(&asm, code);
        dasm_free(&asm);

#ifdef __APPLE__
        sys_icache_invalidate(code, final_size);
#elif defined(__aarch64__)
        __builtin___clear_cache(code, (char *)code + final_size);
#endif

        mprotect(code, final_size, PROT_READ | PROT_EXEC);

        JitInfo *ji = xmA(sizeof *ji);
        ji->code = code;
        ji->code_size = final_size;
        ji->param_count = param_count;
        ji->bound = bound;
        ji->expr = expr_of(func);
        ji->name = name;
        ji->env = NULL;
        ji->env_count = info[FUN_INFO_CAPTURES];

#if JIT_SCAN_LOG
        LOGX("JIT: compiled %s (%d params, %d bound, %zu bytes native)",
            name, param_count, bound, final_size);
#endif

#ifdef TY_PROFILER
        {
                u64 dt = jit_wall_time() - compile_t0;
                TySpinLockLock(&JitLogMutex);
                jit_total_compile_ns += dt;
                jit_total_native_bytes += final_size;
                xvP(jit_compile_log, ((JitCompileRecord) {
                        .name = name,
                        .class_name = clsn,
                        .expr = expr_of(func),
                        .native_size = final_size,
                        .compile_time_ns = dt,
                        .bc_code_size = code_size,
                }));
                TySpinLockUnlock(&JitLogMutex);
        }
#endif

        return ji;
}

// ============================================================================
// Init / Free
// ============================================================================

void
jit_init(Ty *ty)
{
        (void)ty;
#ifdef TY_PROFILER
        TySpinLockInit(&JitLogMutex);
#endif
}

void
jit_free(Ty *ty)
{
        (void)ty;
        // TODO: munmap all cached JIT code
}

#endif // TY_NO_JIT || JIT_ARCH_NONE

/* vim: set sts=8 sw=8 expandtab: */
