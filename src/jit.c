// jit.c - JIT compiler for ty

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>
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
#include "inline.h"
#include "operators.h"
#include "compiler.h"

char JIT;

#define VALUE_SIZE (sizeof (Value))

// ============================================================================
// Value field offsets (must match struct value layout)
// ============================================================================
#define VAL_OFF_TYPE 0
#define VAL_OFF_TAGS 0
#define VAL_OFF_SRC 0
#define VAL_OFF_Z 0
#define VAL_OFF_BOOL 0
#define VAL_OFF_CLASS 0
#define VAL_OFF_OBJECT 0
#define VAL_OFF_INFO 0
#define VAL_OFF_ENV 0
#define VAL_OFF_COUNT 0
#define VAL_OFF_ITEMS 0
#define VAL_OFF_REF 0
#define VAL_OFF_REGEX 0
#define VAL_OFF_STR 0
#define VAL_OFF_BYTES 0
#define VAL_OFF_UOP 0
#define VAL_OFF_BOP 0

#define OFF_TY_STACK  offsetof(Ty, stack)
#define OFF_TY_ST     offsetof(Ty, st)
#define OFF_TY_TLS    offsetof(Ty, tls)
#define OFF_ST_STACK  offsetof(co_state, stack)
#define OFF_ST_FRAMES offsetof(co_state, frames)
#define OFF_ST_RC     offsetof(co_state, rc)
#define OFF_FRAME_FP  offsetof(Frame, fp)
#define OFF_VEC_DATA  offsetof(ValueVector, items)
#define OFF_VEC_LEN   offsetof(ValueVector, count)
#define OFF_DICT_COUNT offsetof(Dict, count)

// TyObject layout:
#define OBJ_OFF_INIT    0    // bool init
#define OBJ_OFF_NSLOT   4    // u32 nslot
#define OBJ_OFF_CLASS   8    // Class *class
#define OBJ_OFF_DYN     offsetof(TyObject, dynamic) // struct itable *dynamic
#define OBJ_OFF_SLOTS   offsetof(TyObject, slots)   // Value slots[] (flexible array)

// ============================================================================
// DynASM runtime includes
// ============================================================================

#include "../dynasm/dasm_proto.h"

#if defined(__aarch64__) || defined(_M_ARM64)
#  include "../dynasm/dasm_arm64.h"
#  include "jit_arm64.h"
#  define JIT_ARCH_ARM64 1
#  define PARAM_REG_BASE 0
#  define SCRATCH_REG_BASE 8
#  define MAX_SCRATCH_REGS 8
#elif defined(__x86_64__) || defined(_M_X64)
#  include "../dynasm/dasm_x86.h"
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

// (JitState removed — resume index is passed as arg, return value encodes reason+idx)

// ============================================================================
// Fast-path statistics (typrof)
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
        _Atomic u64 arith_int;
        _Atomic u64 arith_float;
        _Atomic u64 arith_slow;
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
        SLOW_ARITH,
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
        [SLOW_ARITH]             = "arith",
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

        slow_totals[SLOW_ARITH] += jit_stats.arith_slow;

        u64 total_fast = jit_stats.member_fast + jit_stats.member_set_fast
                       + jit_stats.self_member_read_fast + jit_stats.self_member_write_fast
                       + jit_stats.call_method_baked + jit_stats.call_method_builtin
                       + jit_stats.jeq_int + jit_stats.jeq_str + jit_stats.jeq_nil
                       + jit_stats.jcmp_int
                       + jit_stats.arith_int + jit_stats.arith_float;
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

                u64 arith_fast = jit_stats.arith_int + jit_stats.arith_float;
                fast_path_row(out, "arith", arith_fast, slow_totals[SLOW_ARITH]);
                if (arith_fast + slow_totals[SLOW_ARITH] > 0) {
                        fprintf(out, "      %sint=%llu  float=%llu%s\n",
                                PTERM(90),
                                (unsigned long long)jit_stats.arith_int,
                                (unsigned long long)jit_stats.arith_float,
                                PTERM(0));
                }

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
static void jit_rt_stat_arith_int(void)              { STAT(arith_int); }
static void jit_rt_stat_arith_float(void)            { STAT(arith_float); }

#define EMIT_STAT(fn_ptr) do {                                         \
        jit_emit_load_imm(asm, BC_CALL, (iptr)(fn_ptr));               \
        bc_emit_runtime_call(ctx, BC_CALL);                               \
} while (0)

/* Emit a slow-path record call with 1 operand: jit_rt_slow1(ty, ip, kind, v) */
#define EMIT_SLOW1(bc_ip, kind, val_reg, val_off) do {                           \
        jit_emit_mov(asm, BC_A0, BC_TY);                                         \
        jit_emit_load_imm(asm, BC_A1, (iptr)(bc_ip));                            \
        jit_emit_load_imm(asm, BC_A2, (kind));                                   \
        jit_emit_add_imm(asm, BC_A3, (val_reg), (val_off));                      \
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_slow1);                     \
        bc_emit_runtime_call(ctx, BC_CALL);                                         \
} while (0)

/* Emit a slow-path record call with 2 operands: jit_rt_slow2(ty, ip, kind, a, b) */
#define EMIT_SLOW2(bc_ip, kind, a_reg, a_off, b_reg, b_off) do {                     \
        jit_emit_mov(asm, BC_A0, BC_TY);                                             \
        jit_emit_load_imm(asm, BC_A1, (iptr)(bc_ip));                                \
        jit_emit_load_imm(asm, BC_A2, (kind));                                       \
        jit_emit_add_imm(asm, BC_A3, (a_reg), (a_off));                              \
        jit_emit_add_imm(asm, BC_A4, (b_reg), (b_off));                              \
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_slow2);                         \
        bc_emit_runtime_call(ctx, BC_CALL);                                             \
} while (0)

/* Store bytecode IP in TLS before calling a runtime helper that has no room for an IP arg */
#define EMIT_SET_CALL_IP(bc_ip) do {                                   \
        jit_emit_load_imm(asm, BC_A0, (iptr)(bc_ip));                  \
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_set_call_ip);     \
        bc_emit_runtime_call(ctx, BC_CALL);                               \
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
        bc_emit_runtime_call(ctx, BC_CALL);                                                    \
} while (0)
#else
#define DBG(fmt, ...)
#endif

#define XDBG(fmt, ...) do {                                                                 \
        jit_emit_mov(asm, BC_A0, BC_TY);                                                    \
        jit_emit_load_imm(asm, BC_A1, ctx->sp);                                             \
        jit_emit_load_imm(asm, BC_A2, ((iptr)xfmt(fmt __VA_OPT__(,) __VA_ARGS__)));         \
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_dbg);                                  \
        bc_emit_runtime_call(ctx, BC_CALL);                                                    \
} while (0)

#define TOP_OF_STACK(v) (vN(STACK) = ((v) - vv(STACK)) + 1)

static void
jit_rt_dbg(Ty *ty, i64 sp, char const *msg)
{
        //usize fp = vvL(ty->st->frames)->fp;
        //usize bp = fp + vvL(ty->st->frames)->f.info[FUN_INFO_BOUND];
        //Value const *v = v_(STACK, bp + sp - 1);

        //char const *repr = (sp == 0) ? "<>" : SHOW(v, BASIC, ABBREV);

        //XPRINT_CTX("%sJIT%s [%zu]: %s%s%s: %s", TERM(91), TERM(0), (usize)(bp + sp - 1 - fp), TERM(34), msg, TERM(0), repr);

        CO_LOG("[jit]", TERM(31;1), "%s: %s", msg, SHOW(vvL(STACK), BASIC, ABBREV));
}

static void
jit_rt_itrc(Ty *ty, i64 sp, char const *msg)
{

        //int fp = vvL(ty->st->frames)->fp;
        //int np = vvL(ty->st->frames)->f.info[FUN_INFO_PARAM_COUNT];
        //Value const *f = &vvL(ty->st->frames)->f;

        CO_LOG("[jit]", TERM(31;1), "%s", msg);
}

static void
jit_rt_idbg(Ty *ty, i64 sp, char const *op)
{

        int fp = vvL(ty->st->frames)->fp;
        int np = V_INFO(vvL(ty->st->frames)->f)[FUN_INFO_PARAM_COUNT];
        Value const *f = &vvL(ty->st->frames)->f;

        char *self;
        if (class_of(f) != -1) {
                self = SHOW(&vv(STACK)[fp + np], BASIC, ABBREV);
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

static int
jit_rt_numeric_compare(Value const *a, Value const *b, int op)
{
        double x, y;
        if (nanbox_is_int(a->bits)) x = nanbox_to_int(a->bits);
        else if (nanbox_is_double(a->bits)) x = nanbox_to_double(a->bits);
        else return 2;
        if (nanbox_is_int(b->bits)) y = nanbox_to_int(b->bits);
        else if (nanbox_is_double(b->bits)) y = nanbox_to_double(b->bits);
        else return 2;
        switch (op) { case 0: return x < y; case 1: return x > y;
                      case 2: return x <= y; default: return x >= y; }
}

static void
jit_rt_add(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                *result = INTEGER(V_Z(*a) + V_Z(*b));
                return;
        }

        STAT(arith_slow);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_ADD, a, b);
        *v_(STACK, idx) = val;
}

static void
jit_rt_sub(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                *result = INTEGER(V_Z(*a) - V_Z(*b));
                return;
        }

        STAT(arith_slow);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_SUB, a, b);
        *v_(STACK, idx) = val;
}

static void
jit_rt_mul(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                *result = INTEGER(V_Z(*a) * V_Z(*b));
                return;
        }

        STAT(arith_slow);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_MUL, a, b);
        *v_(STACK, idx) = val;
}

static void
jit_rt_div(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                if (V_Z(*(b)) == 0) ZeroDividePanic(ty);
                *result = INTEGER(V_Z(*a) / V_Z(*b));
                return;
        }

        STAT(arith_slow);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_DIV, a, b);
        *v_(STACK, idx) = val;
}

static void
jit_rt_mod(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                if (V_Z(*(b)) == 0) ZeroDividePanic(ty);
                *result = INTEGER(V_Z(*a) % V_Z(*b));
                return;
        }

        STAT(arith_slow);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_MOD, a, b);
        *v_(STACK, idx) = val;
}

static void
jit_rt_neg(Ty *ty, Value *result, Value *a)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER) {
                *result = INTEGER(-V_Z(*a));
                return;
        }

        if (V_TYPE(*(a)) == VALUE_REAL) {
                *result = REAL(-V_REAL(*a));
                return;
        }

        vN(STACK) = (result - vv(STACK)) + 1;

        vm_jit_neg(ty);
}

static void
jit_rt_not(Ty *ty, Value *result, Value *a)
{
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 1;
        Value val = BOOLEAN(!value_truthy(ty, a));
        *v_(STACK, idx) = val;
}

static void
jit_rt_eq(Ty *ty, Value *result, Value *a, Value *b)
{
        if (LIKELY(V_TYPE(*a) == VALUE_NIL || V_TYPE(*b) == VALUE_NIL)) {
                *result = BOOLEAN(V_TYPE(*a) == V_TYPE(*b));
                return;
        }

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = BOOLEAN(value_test_equality(ty, a, b));
        *v_(STACK, idx) = val;
}

static void
jit_rt_ne(Ty *ty, Value *result, Value *a, Value *b)
{
        if (LIKELY(V_TYPE(*a) == VALUE_NIL || V_TYPE(*b) == VALUE_NIL)) {
                *result = BOOLEAN(V_TYPE(*a) != V_TYPE(*b));
                return;
        }

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = BOOLEAN(!value_test_equality(ty, a, b));
        *v_(STACK, idx) = val;
}

static int
jit_rt_str_eq(Value *a, Value *b)
{
        return (V_BYTES(*(a)) == V_BYTES(*(b)))
            && (memcmp(V_STR(*(a)), V_STR(*(b)), V_BYTES(*(a))) == 0);
}

static void
jit_rt_lt(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                *result = BOOLEAN(V_Z(*a) < V_Z(*b));
                return;
        }

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        DoLt(ty);
}

static void
jit_rt_le(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                *result = BOOLEAN(V_Z(*a) <= V_Z(*b));
                return;
        }

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        DoLeq(ty);
}

static void
jit_rt_gt(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                *result = BOOLEAN(V_Z(*a) > V_Z(*b));
                return;
        }

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        DoGt(ty);
}

static void
jit_rt_ge(Ty *ty, Value *result, Value *a, Value *b)
{
        if (V_TYPE(*(a)) == VALUE_INTEGER && V_TYPE(*(b)) == VALUE_INTEGER) {
                *result = BOOLEAN(V_Z(*a) >= V_Z(*b));
                return;
        }

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

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

        Class *cls = class_get(ty, V_CLASS(*(self)));

        if (!cls->final) {
                LOGX("  Class is not final, cannot use fast path");
                return;
        }

        if (!V_OBJECT(*(self))->init) {
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
                                        SHOW(&V_OBJECT(*self)->slots[off & OFF_MASK], BASIC, ABBREV)
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
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 1;

        if (obj == NULL) {
                obj = vm_get_self(ty);
                v_L(STACK) = *obj;
        }

        if (V_TYPE(*(obj)) == VALUE_OBJECT) {
                Class *cls = class_get(ty, V_CLASS(*(obj)));
                if (member_id < vN(cls->offsets_r)) {
                        u16 off = v__(cls->offsets_r, member_id);
                        if (off != OFF_NOT_FOUND) {
                                u8 kind = (off >> OFF_SHIFT);
                                if (kind == OFF_FIELD) {
                                        STAT(member_fast);
                                        *result = V_OBJECT(*(obj))->slots[off & OFF_MASK];
                                        return;
                                }
                        }
                }
        }

        STAT(member_slow);
        Value value = vm_jit_member_access(ty, member_id);
        vN(STACK) = idx + 1;
        *v_(STACK, idx) = value;
}

static void
jit_rt_try_member(Ty *ty, Value *top, int member_id)
{
        vN(STACK) = top - vv(STACK);
        vm_jit_try_member_access(ty, member_id);
}

static void
jit_rt_get_member(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        vm_jit_get_member(ty);
}

#define JIT_RT_MUT_OP(op, vm_op)                                                           \
        static void                                                                        \
        jit_rt_mut_##op(Ty *ty, Value *target, Value *val, Value *result)                  \
        {                                                                                  \
                if (V_TYPE(*target) == VALUE_INTEGER && V_TYPE(*val) == VALUE_INTEGER) {   \
                        imax a = V_Z(*target);                                              \
                        imax b = V_Z(*val);                                                 \
                        imax z = a;                                                         \
                        if ((void *)vm_op == (void *)DoMutAdd) z = a + b;                  \
                        else if ((void *)vm_op == (void *)DoMutSub) z = a - b;             \
                        else if ((void *)vm_op == (void *)DoMutMul) z = a * b;             \
                        else goto slow;                                                     \
                        *target = *result = INTEGER(z);                                     \
                        return;                                                             \
                }                                                                          \
                if (V_TYPE(*target) == VALUE_REAL && V_TYPE(*val) == VALUE_REAL) {         \
                        double a = V_REAL(*target);                                         \
                        double b = V_REAL(*val);                                            \
                        double z = a;                                                       \
                        if ((void *)vm_op == (void *)DoMutAdd) z = a + b;                  \
                        else if ((void *)vm_op == (void *)DoMutSub) z = a - b;             \
                        else if ((void *)vm_op == (void *)DoMutMul) z = a * b;             \
                        else if ((void *)vm_op == (void *)DoMutDiv) z = a / b;             \
                        else goto slow;                                                     \
                        *target = *result = REAL(z);                                        \
                        return;                                                             \
                }                                                                          \
        slow:                                                                             \
                ptrdiff_t idx = result - vv(STACK);                                        \
                vN(STACK) = val - vv(STACK) + 1;                                           \
                vm_jit_push_target(ty, target);                                            \
                vm_op(ty, true);                                                           \
                *v_(STACK, idx) = *vm_get(ty, 0);                                          \
        }                                                                                  \
                                                                                           \
        static void                                                                        \
        jit_rt_member_mut_##op(Ty *ty, Value *obj, int m_id, Value *val, Value *result)    \
        {                                                                                  \
                ptrdiff_t idx = result - vv(STACK);                                        \
                vN(STACK) = val - vv(STACK) + 1;                                           \
                DoTargetMember(ty, *obj, m_id);                                            \
                vm_op(ty, true);                                                           \
                *v_(STACK, idx) = *vm_get(ty, 0);                                          \
        }                                                                                  \
        static void                                                                        \
        jit_rt_subscript_mut_##op(Ty *ty, Value *val, Value *xs, Value *ix)                \
        {                                                                                  \
                if (V_TYPE(*xs) == VALUE_ARRAY && V_TYPE(*ix) == VALUE_INTEGER) {          \
                        imax i = V_Z(*ix);                                                  \
                        isize n = vN(*V_ARRAY(*xs));                                        \
                        if (i < 0) i += n;                                                  \
                        if (i >= 0 && i < n) {                                              \
                                Value *target = v_(*V_ARRAY(*xs), i);                       \
                                if (V_TYPE(*target) == VALUE_INTEGER                        \
                                    && V_TYPE(*val) == VALUE_INTEGER) {                     \
                                        imax a = V_Z(*target), b = V_Z(*val), z = a;        \
                                        if ((void *)vm_op == (void *)DoMutAdd) z = a + b;  \
                                        else if ((void *)vm_op == (void *)DoMutSub) z = a - b; \
                                        else if ((void *)vm_op == (void *)DoMutMul) z = a * b; \
                                        else goto slow_sub;                                 \
                                        *target = *val = INTEGER(z);                        \
                                        return;                                             \
                                }                                                          \
                        }                                                                  \
                }                                                                          \
        slow_sub:                                                                          \
                ptrdiff_t idx = val - vv(STACK);                                           \
                vN(STACK) = val - vv(STACK) + 1;                                           \
                xvP(STACK, *xs);                                                           \
                xvP(STACK, *ix);                                                           \
                DoTargetSubscript(ty);                                                     \
                vm_op(ty, true);                                                           \
                *v_(STACK, idx) = *vm_get(ty, 0);                                          \
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
        vN(STACK) = val - vv(STACK) + 1;
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
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx;
        Value val = compiler_render_template(ty, (Expr *)expr_ptr);
        *v_(STACK, idx) = val;
}

static int
jit_rt_ensure_len_tuple(Value const *tos, int expected)
{
        return V_TYPE(*(tos)) == VALUE_TUPLE && V_COUNT(*(tos)) <= expected;
}

static int
jit_rt_is_type(Value const *value, int expected)
{
        return V_TYPE(*value) == expected;
}

static int
jit_rt_index_tuple(Value *tos, Value *dst, int i)
{
        if (V_TYPE(*(tos)) != VALUE_TUPLE || V_COUNT(*(tos)) <= i) {
                return 0;
        }
        *dst = V_ITEMS(*(tos))[i];
        return 1;
}

static int
jit_rt_try_tuple_member(Value *tos, Value *dst, bool required, int name_id)
{
        if (V_TYPE(*(tos)) != VALUE_TUPLE) {
                return 0;
        }

        if (V_IDS(*(tos)) != NULL) {
                for (int i = 0; i < V_COUNT(*(tos)); ++i) {
                        if (V_IDS(*(tos))[i] == name_id) {
                                *dst = V_ITEMS(*(tos))[i];
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
        if (V_TAGS(*(tos)) > 0) {
                *target = TAG(tags_first(ty, V_TAGS(*tos)));
                (PopTag)(ty, tos);
                return 1;
        }

        return 0;
}

static int
jit_rt_try_assign_non_nil(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        Value *target = vm_jit_pop_target(ty);
        if (V_TYPE(v_L(STACK)) == VALUE_NIL) return 0;
        *target = v_L(STACK);
        return 1;
}

static void
jit_rt_tag_push(Ty *ty, Value *v, int tag)
{
        *v = value_with_tags(ty, *v, tags_push(ty, V_TAGS(*v), tag));
}

static int
jit_rt_try_regex(Ty *ty, Value *str, Regex *re, Value *top)
{
        vN(STACK) = top - vv(STACK);
        Value regex = REGEX(re);
        xvP(STACK, regex);
        if (V_TYPE(*(str)) == VALUE_STRING) {
                Value result = string_match(ty, str, 1, NULL);
                if (V_TYPE(result) != VALUE_NIL) {
                        *vvL(STACK) = result;
                        return 1;
                }
        }
        vvX(STACK);
        return 0;
}

static void
jit_rt_assign_regex_matches(Ty *ty, Value *match, int n)
{
        Value *vp = vm_jit_pop_target(ty);
        if (V_TYPE(*(match)) == VALUE_ARRAY) {
                int i = 0;
                for (; i < vN(*V_ARRAY(*match)); ++i) {
                        vp[i] = v__(*V_ARRAY(*match), i);
                }
                while (i < n + 1) {
                        vp[i++] = NIL;
                }
        } else {
                *vp = *match;
        }
}

static i32
jit_rt_match_tag_id(Ty *ty, Value const *v, int wrapped)
{
        if (wrapped) {
                if (!(V_TYPE(*v) & VALUE_TAGGED)) return -1;
                return tags_first(ty, V_TAGS(*v));
        }
        return V_TYPE(*v) == VALUE_TAG ? V_TAG(*v) : -1;
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

static void
jit_rt_function(Ty *ty, Value *top, char const *ip)
{
        vN(STACK) = top - vv(STACK);
        (void)DoFunction(ty, ip);
}

static void
jit_rt_generator(Ty *ty, Value *top, char const *ip)
{
        vN(STACK) = top - vv(STACK);
        (void)DoGenerator(ty, ip);
}

static void
jit_rt_patch_env(Ty *ty, Value *top, int n)
{
        (void)ty;
        *V_ENV(*top)[n] = *top;
}

static void
jit_rt_push_index(Ty *ty, Value *result, int n)
{
        *result = INDEX(0, 0, n);
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
                if (V_TYPE(*(result)) == VALUE_OBJECT) {
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
                                vp = &V_OBJECT(*(result))->slots[off & OFF_MASK];
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
        if (V_TYPE(*(tos)) != VALUE_ARRAY) {
                return 0;
        }

        int idx = i;
        if (idx < 0) {
                idx += vN(*V_ARRAY(*tos));
        }

        if (vN(*V_ARRAY(*tos)) <= idx) {
                if (required) {
                        return 0;
                } else {
                        *dst = NIL;
                        return 1;
                }
        }

        *dst = v__(*V_ARRAY(*tos), idx);

        return 1;
}

static void
jit_rt_tuple(Ty *ty, Value *top, i32 n, i32 *ids)
{
        vN(STACK) = top - vv(STACK);

        Value tuple = value_tuple_alloc(ty, n, ids != NULL);
        Value *items = V_ITEMS(tuple);
        if (ids != NULL) memcpy(V_IDS(tuple), ids, n * sizeof (i32));

        memcpy(items, vZ(STACK) - n, n * sizeof (Value));
        vN(STACK) -= n;

        xvP(STACK, tuple);
}

static void
jit_rt_subscript(Ty *ty, Value *top)
{
        ptrdiff_t idx = (top - vv(STACK));
        vN(STACK) = idx + 2;
        DoSubscript(ty, true);
}

static bool
jit_rt_array_index(Value const *array, Value const *index, isize *out)
{
        if (V_TYPE(*array) != VALUE_ARRAY || V_TYPE(*index) != VALUE_INTEGER) return false;
        isize count = vN(*V_ARRAY(*array));
        imax i = V_Z(*index);
        if (i < 0) i += count;
        if (i < 0 || i >= count) return false;
        *out = i;
        return true;
}

static void
jit_rt_array_get(Ty *ty, Value *result, Value const *array, Value const *index)
{
        isize i;
        if (jit_rt_array_index(array, index, &i)) {
                *result = v__(*V_ARRAY(*array), i);
                return;
        }
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;
        DoSubscript(ty, true);
}

static void
jit_rt_array_set(Value const *value, Value *array, Value const *index)
{
        *v_(*V_ARRAY(*array), V_Z(*index)) = *value;
}

static void
jit_rt_array_set_semantic(Ty *ty, Value *top, int n)
{
        ptrdiff_t count = top - vv(STACK);
        if (n == 1 && count >= 3) {
                Value *value = top - 3;
                Value *array = top - 2;
                Value *index = top - 1;
                if (V_TYPE(*array) == VALUE_ARRAY && V_TYPE(*index) == VALUE_INTEGER) {
                        imax i = V_Z(*index);
                        isize count = vN(*V_ARRAY(*array));
                        if (i < 0) i += count;
                        if (i >= 0 && i < count) {
                                *v_(*V_ARRAY(*array), i) = *value;
                                return;
                        }
                }
        }
        vN(STACK) = count;
        DoAssignSubscript(ty, n, true);
}

static void
jit_rt_array_add(Ty *ty, Value *value, Value *array, Value const *index)
{
        Value *slot = v_(*V_ARRAY(*array), V_Z(*index));
        if (V_TYPE(*slot) == VALUE_REAL && V_TYPE(*value) == VALUE_REAL) {
                *slot = *value = REAL(V_REAL(*slot) + V_REAL(*value));
        } else if (V_TYPE(*slot) == VALUE_INTEGER && V_TYPE(*value) == VALUE_INTEGER) {
                *slot = *value = INTEGER(V_Z(*slot) + V_Z(*value));
        } else {
                *slot = *value = vm_2op(ty, OP_ADD, slot, value);
        }
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

static void
jit_rt_post_inc(Ty *ty, Value *v, Value *top)
{
        vN(STACK) = top - vv(STACK);
        xvP(STACK, *v);
        IncValue(ty, v);
}

static void
jit_rt_post_inc_subscript(Ty *ty, Value *xs, Value *ix, Value *top)
{
        vN(STACK) = top - vv(STACK);

        Value _xs = *xs;
        Value _ix = *ix;

        xvP(STACK, _xs);
        xvP(STACK, _ix);
        DoTargetSubscript(ty);

        Value *x = vm_jit_pop_target(ty);

        xvP(STACK, *x);
        IncValue(ty, x);
}

static void
jit_rt_post_dec(Ty *ty, Value *v, Value *top)
{
        vN(STACK) = top - vv(STACK);
        xvP(STACK, *v);
        DecValue(ty, v);
}

static void
jit_rt_post_dec_subscript(Ty *ty, Value *xs, Value *ix, Value *top)
{
        vN(STACK) = top - vv(STACK);

        Value _xs = *xs;
        Value _ix = *ix;

        xvP(STACK, _xs);
        xvP(STACK, _ix);
        DoTargetSubscript(ty);

        Value *x = vm_jit_pop_target(ty);

        xvP(STACK, *x);
        DecValue(ty, x);
}

static void
jit_rt_pre_inc(Ty *ty, Value *v, Value *top)
{
        vN(STACK) = top - vv(STACK);
        IncValue(ty, v);
        xvP(STACK, *v);
}

static void
jit_rt_pre_inc_subscript(Ty *ty, Value *xs, Value *ix, Value *top)
{
        vN(STACK) = top - vv(STACK);

        Value _xs = *xs;
        Value _ix = *ix;

        xvP(STACK, _xs);
        xvP(STACK, _ix);
        DoTargetSubscript(ty);

        Value *x = vm_jit_pop_target(ty);

        IncValue(ty, x);
        xvP(STACK, *x);
}

static void
jit_rt_pre_dec(Ty *ty, Value *v, Value *top)
{
        vN(STACK) = top - vv(STACK);
        DecValue(ty, v);
        xvP(STACK, *v);
}

static void
jit_rt_pre_dec_subscript(Ty *ty, Value *xs, Value *ix, Value *top)
{
        vN(STACK) = top - vv(STACK);

        Value _xs = *xs;
        Value _ix = *ix;

        xvP(STACK, _xs);
        xvP(STACK, _ix);
        DoTargetSubscript(ty);

        Value *x = vm_jit_pop_target(ty);

        DecValue(ty, x);
        xvP(STACK, *x);
}

static void
jit_rt_post_inc_member(Ty *ty, Value *obj, int member_id, Value *top)
{
        vN(STACK) = top - vv(STACK);
        DoTargetMember(ty, *obj, member_id);
        Value *x = vm_jit_pop_target(ty);
        xvP(STACK, *x);
        IncValue(ty, x);
}

static void
jit_rt_post_dec_member(Ty *ty, Value *obj, int member_id, Value *top)
{
        vN(STACK) = top - vv(STACK);
        DoTargetMember(ty, *obj, member_id);
        Value *x = vm_jit_pop_target(ty);
        xvP(STACK, *x);
        DecValue(ty, x);
}

static void
jit_rt_pre_inc_member(Ty *ty, Value *obj, int member_id, Value *top)
{
        vN(STACK) = top - vv(STACK);
        DoTargetMember(ty, *obj, member_id);
        Value *x = vm_jit_pop_target(ty);
        IncValue(ty, x);
        xvP(STACK, *x);
}

static void
jit_rt_pre_dec_member(Ty *ty, Value *obj, int member_id, Value *top)
{
        vN(STACK) = top - vv(STACK);
        DoTargetMember(ty, *obj, member_id);
        Value *x = vm_jit_pop_target(ty);
        DecValue(ty, x);
        xvP(STACK, *x);
}

// String literal: mirrors static DoStringLiteral in vm.c
static void
jit_rt_string(Ty *ty, Value *result, i32 i)
{
        InternEntry const *interned = intern_entry(&xD.strings, i);
        *result = STRING_NOGC(ty, interned->name, (uptr)interned->data);
}


static char const *
jit_skip_local_operand(char const *ip)
{
        ip += sizeof(int);
#ifndef TY_NO_LOG
        ip += strlen(ip) + 1;
#endif
        return ip;
}


static char const *
jit_skip_member_operand(char const *ip)
{
#ifndef TY_NO_LOG
        ip += strlen(ip) + 1;
#endif
        return ip;
}



static bool
jit_simple_ctor_plan(Ty *ty, int class_id, int argc, u64 *packed, bool *nil_guard)
{
        Class *class = class_get(ty, class_id);
        if (!class->really_final) return false;
        Value *ctor = class_ctor(ty, class_id);
        if (ctor == NULL || V_TYPE(*ctor) != VALUE_FUNCTION
            || argc != param_count_of(ctor) || argc <= 0 || argc > 8
            || rest_idx_of(ctor) != -1 || kwargs_idx_of(ctor) != -1)
                return false;
        char const *ip = code_of(ctor), *end = ip + code_size_of(ctor);
        int self_local = argc;
        u64 map = 0;
        unsigned seen = 0;
        bool defaults = false;
        while (ip < end) {
                u8 op = (u8)*ip++;
                if (op == INSTR_LOAD_LOCAL) {
                        i32 local;
                        if (ip + sizeof local > end) return false;
                        __builtin_memcpy(&local, ip, sizeof local); ip += sizeof local;
#ifndef TY_NO_LOG
                        ip += strlen(ip) + 1;
                        if (ip > end) return false;
#endif
                        if (local < 0 || local >= argc) { defaults = true; continue; }
                        char const *p = ip;
                        if (p >= end || (u8)*p++ != INSTR_LOAD_LOCAL) { defaults = true; continue; }
                        i32 self;
                        if (p + sizeof self > end) return false;
                        __builtin_memcpy(&self, p, sizeof self); p += sizeof self;
#ifndef TY_NO_LOG
                        p += strlen(p) + 1;
                        if (p > end) return false;
#endif
                        if (self != self_local || p >= end || (u8)*p++ != INSTR_TARGET_MEMBER)
                                { defaults = true; continue; }
                        i32 member;
                        if (p + sizeof member > end) return false;
                        __builtin_memcpy(&member, p, sizeof member); p += sizeof member;
                        Class *c = class_get(ty, class_id);
                        if (member < 0 || member >= vN(c->offsets_w)) return false;
                        u16 off = v__(c->offsets_w, member);
                        if ((off >> OFF_SHIFT) != OFF_FIELD || (off & OFF_MASK) > 255) return false;
                        if (p >= end || (u8)*p++ != INSTR_ASSIGN) return false;
                        if (p < end && (u8)*p == INSTR_POP) ++p;
                        map |= (u64)(off & OFF_MASK) << (local * 8);
                        seen |= 1u << local;
                        ip = p;
                        continue;
                }
                switch (op) {
                case INSTR_JUMP_IF_NIL: defaults = true; ip += sizeof(i32); break;
                case INSTR_JUMP: ip += sizeof(i32); break;
                case INSTR_REAL: ip += sizeof(double); break;
                case INSTR_INT8: ip += sizeof(i8); break;
                case INSTR_INTEGER: ip += sizeof(imax); break;
                case INSTR_ASSIGN_LOCAL: ip += sizeof(i32);
#ifndef TY_NO_LOG
                        ip += strlen(ip) + 1;
#endif
                        break;
                case INSTR_RETURN: break;
                default: return false;
                }
                if (ip > end) return false;
        }
        if (seen != ((1u << argc) - 1)) return false;
        *packed = map;
        *nil_guard = defaults;
        return true;
}

static int
jit_rt_simple_ctor(Ty *ty, Value *result, int class_id, int argc, u64 packed, int nil_guard)
{
        Value *callee = result + argc;
        if (V_TYPE(*callee) != VALUE_CLASS || V_CLASS(*callee) != class_id) return 0;
        if (nil_guard) {
                for (int i = 0; i < argc; ++i)
                        if (V_TYPE(result[i]) == VALUE_NIL) return 0;
        }
        Value object = RawObject(class_id);
        TyObject *o = V_OBJECT(object);
        for (int i = 0; i < argc; ++i)
                o->slots[(packed >> (i * 8)) & 0xff] = result[i];
        o->init = true;
        *result = object;
        return 1;
}

static void
jit_rt_class(Ty *ty, Value *result, i32 class_id)
{
        *result = CLASS(class_id);
}

static int
jit_rt_numeric_pow(Ty *ty, Value *base, Value const *exponent)
{
        Value a = *base;
        Value b = *exponent;
        if ((V_TYPE(a) != VALUE_INTEGER && V_TYPE(a) != VALUE_REAL)
            || (V_TYPE(b) != VALUE_INTEGER && V_TYPE(b) != VALUE_REAL)) {
                return false;
        }
        double x = V_TYPE(a) == VALUE_INTEGER ? (double)V_Z(a) : V_REAL(a);
        double y = V_TYPE(b) == VALUE_INTEGER ? (double)V_Z(b) : V_REAL(b);
        double result = pow(x, y);
        *base = V_TYPE(a) == VALUE_INTEGER && V_TYPE(b) == VALUE_INTEGER
                ? INTEGER((i64)result) : REAL(result);
        return true;
}

static void
jit_rt_binary_op(Ty *ty, Value *top, int op)
{
        vN(STACK) = top - vv(STACK);
        DoBinaryOp(ty, op, true);
}

static void
jit_rt_call_global_kw(Ty *ty, Value *top, int gi, int n, int nkw, char *kw_ip)
{
        vN(STACK) = top - vv(STACK);
        Value kwargs = BuildKwargsDict(ty, &kw_ip, nkw);
        DoCallEx(ty, v_(Globals, gi), n, &kwargs, true);
}

static void
jit_rt_call_kw(Ty *ty, Value *top, int n, int nkw, char *kw_ip)
{
        vN(STACK) = top - vv(STACK);
        Value f = vXx(STACK);
        Value kwargs = BuildKwargsDict(ty, &kw_ip, nkw);
        DoCallEx(ty, &f, n, &kwargs, true);
}

static void
jit_rt_call_method_kw(Ty *ty, Value *top, int z, int n, int nkw, char *kw_ip)
{
        vN(STACK) = top - vv(STACK);
        char *saved = ty->ip;
        ty->ip = kw_ip;
        CallMethod(ty, z, n, nkw, false, true);
        ty->ip = saved;
}

// Three-way compare => Value (wraps value_compare into INTEGER)
static void
jit_rt_cmp(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + 2;
        DoCmp(ty);
}

// Count (#v) => Value
static void
jit_rt_count(Ty *ty, Value *result, Value *v)
{
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 1;
        DoCount(ty, true);
}

static void
jit_rt_tls0(Ty *ty, Value *top, int n)
{
        vN(STACK) = top - vv(STACK);

        while (vN(ty->tls) <= n) {
                xvP(ty->tls, NONE);
        }

        vm_exec(ty, v__(xD.tls0, n));
}

// Subscript assign: container[subscript] = value
// Stack layout: value, container, subscript (TOS)
// Pops all 3
static void
jit_rt_assign_subscript(Ty *ty, Value *top, int n)
{
        vN(STACK) = top - vv(STACK);
        DoAssignSubscript(ty, n, true);
}

// Create array from N values on the JIT operand stack
static void
jit_rt_array(Ty *ty, Value *result, Value *elements, int n)
{
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + n;
        Array *xs = vAn(n);
        vN(*xs) = n;
        memcpy(vv(*xs), v_(STACK, idx), n * sizeof (Value));
        *v_(STACK, idx) = ARRAY(xs);
}

// Create empty array
static void
jit_rt_array0(Ty *ty, Value *result)
{
        *result = ARRAY(uAo0(sizeof (Array), GC_ARRAY));
}


static void
jit_rt_swap_subscripts(Ty *ty, Value *array, Value *ia, Value *ib)
{
        Value a = *array, i = *ia, j = *ib;
        isize base = vN(STACK);
        xvP(STACK, a); xvP(STACK, i); DoSubscript(ty, true);
        xvP(STACK, a); xvP(STACK, j); DoSubscript(ty, true);
        /* Keep both results rooted while performing semantic assignments. */
        Value vi = v_(STACK, base)[0], vj = v_(STACK, base)[1];
        xvP(STACK, vj); xvP(STACK, a); xvP(STACK, i); DoAssignSubscript(ty, 1, true);
        xvP(STACK, vi); xvP(STACK, a); xvP(STACK, j); DoAssignSubscript(ty, 1, true);
        vN(STACK) = base;
}

static void
jit_rt_array_compr(Ty *ty, Value *top, i32 idx, i32 n)
{
        vN(STACK) = top - vv(STACK);
        Value *array = vZ(STACK) - (idx + n + 1);
        vvPn(*V_ARRAY(*array), vZ(STACK) - n, n);
        vN(STACK) -= n;
}

// CALL_STATIC_METHOD: push CLASS value as self, then CallMethod
static void
jit_rt_call_static_method(Ty *ty, Value *result, int class_id, int argc, int method_id, int nkw)
{
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + argc;
        xvP(STACK, CLASS(class_id));
        CallMethod(ty, method_id, argc, nkw, true, true);
        *result = *vm_pop(ty);
}

static void
jit_rt_default_dict(Ty *ty, Value *top, i32 n)
{
        ptrdiff_t idx = top - vv(STACK);
        vN(STACK) = idx;
        Value dflt = vXx(STACK);
        DoDictLiteral(ty, n, &dflt);
}

static void
jit_rt_dict(Ty *ty, Value *top, i32 n)
{
        ptrdiff_t idx = top - vv(STACK);
        vN(STACK) = idx;
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
        ptrdiff_t idx = (exc - vv(STACK));
        vN(STACK) = idx + 1;
        vm_throw(ty, exc);
}

// BAD_MATCH: tag TOS with MatchError and throw
static void
jit_rt_bad_match(Ty *ty, Value *v)
{
        *v = value_with_tags(ty, *v, tags_push(ty, V_TAGS(*v), TAG_MATCH_ERR));
        vm_throw(ty, v);
}

// RANGE: create a range object
static void
jit_rt_range(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + 2;
        Value val = vm_make_range(ty, a, b, false);
        *v_(STACK, idx) = val;
}

// INCRANGE: create an inclusive range object
static void
jit_rt_incrange(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + 2;
        Value val = vm_make_range(ty, a, b, true);
        *v_(STACK, idx) = val;
}

// TO_STRING: convert value to string
static void
jit_rt_to_string(Ty *ty, Value *val)
{
        if (V_TYPE(*(val)) == VALUE_STRING) {
                return;
        }

        if (UNLIKELY(V_TYPE(*val) == VALUE_PTR)) {
                char *show = VSC(val);
                *val = STRING_NOGC(ty, show, strlen(show));
                return;
        }

        ptrdiff_t idx = (val - vv(STACK));
        vN(STACK) = idx + 1;
        CallMethod(ty, NAMES._str_, 0, 0, false, true);
}

// ASSIGN_GLOBAL: set global[n] = value
static void
jit_rt_assign_global(Ty *ty, int n, Value *val)
{
        *vm_global(ty, n) = *val;
}

// TRY: push try block, sync stack, return jmp_buf pointer for _setjmp
static void *
jit_rt_push_try(Ty *ty, Value *top, char *catch_addr, char *finally_addr, char *end_addr)
{
        TOP_OF_STACK(top);
        return vm_jit_push_try(ty, catch_addr, finally_addr, end_addr);
}

// CATCH: pop throw context, set state to TRY_FINALLY
static void
jit_rt_catch(Ty *ty)
{
        vXx(ty->throw_stack);
        v_L(ty->st->try_stack)->state = TRY_FINALLY;
}

// RETHROW: set state to TRY_THROW, end to NULL (triggers re-throw at END_TRY)
static void
jit_rt_rethrow_setup(Ty *ty)
{
        struct try *t = ty->st->try_stack.items[ty->st->try_stack.count - 1];
        t->state = TRY_THROW;
        t->end = NULL;
}

// FINALLY instruction: set state to TRY_FINALLY, save resume address
static void
jit_rt_finally_enter(Ty *ty, char *resume_addr)
{
        struct try *t = ty->st->try_stack.items[ty->st->try_stack.count - 1];
        t->state = TRY_FINALLY;
        t->end = resume_addr;
}

// END_TRY: pop try block, return end pointer (NULL means re-throw needed)
static char *
jit_rt_end_try(Ty *ty)
{
        return vXx(ty->st->try_stack)->end;
}

// ARRAY_REST: extract sub-array from index 'start', excluding 'suffix' elements at end
// Returns 1 on success, 0 on failure
static int
jit_rt_array_rest(Ty *ty, Value *tos, i32 start, i32 suffix)
{
        Value *target = vm_jit_pop_target(ty);
        return vm_jit_array_rest(ty, tos, target, start, suffix) ? 1 : 0;
}

// TUPLE_REST: extract remaining tuple elements from index 'start'
// Returns 1 on success (target written), 0 on failure (not a tuple)
static int
jit_rt_tuple_rest(Ty *ty, Value *tos, i32 start)
{
        Value *target = vm_jit_pop_target(ty);
        return vm_jit_tuple_rest(ty, tos, target, start) ? 1 : 0;
}

// RECORD_REST: extract fields not in excluded list
// Returns 1 on success, 0 on failure (not a tuple/record)
static int
jit_rt_record_rest(Ty *ty, Value *tos, i32 const *excluded_ids)
{
        Value *target = vm_jit_pop_target(ty);
        return vm_jit_record_rest(ty, tos, target, excluded_ids) ? 1 : 0;
}

#if JIT_ARCH_ARM64
// ARM64 callee-saved register assignments
#define BC_TY    19   // x19
#define BC_RESUME 20  // x20 - resume index (2nd arg, saved for dispatch)
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
#define BC_CACHE_MASK BC_RESUME
#define BC_RAW0 12
#define BC_RAW1 13
#elif JIT_ARCH_X64
// x86-64 callee-saved register assignments
#define BC_TY    12   // r12
#define BC_RESUME 13  // r13 - resume index (2nd arg, saved for dispatch)
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
#define BC_CACHE_MASK BC_RESUME
#endif

// Pack two 32-bit ints into a single 64-bit immediate for register-only calls
#define PACK32(hi, lo) (((i64)(hi) << 32) | ((i64)(u32)(lo)))

#define MAX_BC_OPS    64   // Max operand stack depth
#define MAX_BC_LABELS 512  // Max DynASM labels
#define MAX_JIT_TRY   8    // Max nested try blocks in JIT

// Try block tracking for JIT compilation
typedef struct {
        int sp;                    // JIT sp at TRY entry
        char const *end_addr;      // bytecode address of end (from TRY operand)
        int finally_label;         // DynASM label for finally code start
        int end_label;             // DynASM label for after try/catch/finally
        // Resume points for FINALLY instructions targeting this try block
        struct {
                char const *addr;  // bytecode address after FINALLY instruction
                int label;         // DynASM label for that resume point
        } finally_resumes[8];
        int n_finally_resumes;
} JitTryInfo;

typedef struct {
        int offset;
        int next;
        int target;
        int block;
        u8 op;
} BcCfgNode;

typedef struct {
        int local;
        int class_id;
        int reg;
} BcRawLocal;

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
        i32 op_known_class[MAX_BC_OPS];

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
        int inline_cost;
        bool registerize;
        bool cfg_has_try;
        bool cfg_has_yield;
        BcCfgNode *cfg_nodes;
        int cfg_count;
        int *cfg_index;
        u8 *cfg_dirty;
        u32 *raw_scores;
        u32 *raw_mutations;
        BcRawLocal raw_locals[2];
        int raw_count;
        u8 raw_dirty;
        int resume_labels[MAX_BC_OPS]; // DynASM labels for resume points

        // Try/catch/finally tracking
        JitTryInfo try_info[MAX_JIT_TRY];
        int try_depth;
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

static bool
bc_cfg_same_block(JitCtx const *ctx, int a, int b, int c);
#ifdef TY_PROFILER
static void
bc_emit_profiler_tick_at(JitCtx *ctx, char const *ip);
#endif

static int
bc_raw_slot(JitCtx const *ctx, int local)
{
        for (int i = 0; i < ctx->raw_count; ++i) {
                if (ctx->raw_locals[i].local == local) {
                        return i;
                }
        }
        return -1;
}

static void
bc_raw_reset(JitCtx *ctx)
{
        if (ctx->raw_count > 0) {
                jit_emit_load_imm(&ctx->asm, BC_CACHE_MASK, 0);
        }
}

static void
bc_emit_runtime_call(JitCtx *ctx, int reg)
{
        bc_raw_reset(ctx);
        jit_emit_call_reg(&ctx->asm, reg);
}

/* Runtime calls that can re-enter Ty may grow STACK and invalidate BC_OPS. */
static void
bc_emit_reentrant_call(JitCtx *ctx, int reg)
{
        bc_emit_runtime_call(ctx, reg);
        jit_emit_reload_stack(&ctx->asm, ctx->bound);
}

static void
bc_raw_kill(JitCtx *ctx, int local)
{
        int slot = bc_raw_slot(ctx, local);
        if (slot < 0) {
                return;
        }
        jit_emit_load_imm(&ctx->asm, BC_S0, ~((i64)1 << slot));
        jit_emit_and(&ctx->asm, BC_CACHE_MASK, BC_CACHE_MASK, BC_S0);
}

static int
bc_raw_ensure(JitCtx *ctx, int local, int class_id, int lbl_slow)
{
        int slot = bc_raw_slot(ctx, local);
        if (slot < 0 || ctx->raw_locals[slot].class_id != class_id) return -1;
        dasm_State **asm = &ctx->asm;
        int lbl_ready = bc_next_label(ctx);
        if (ctx->raw_dirty & ((u8)1 << slot))
                jit_emit_branch_bit_set(asm, BC_CACHE_MASK, slot, lbl_ready);
        int reg = ctx->raw_locals[slot].reg;
        jit_emit_ldr64(asm, reg, BC_LOC, local * VALUE_SIZE);
        if (class_id == CLASS_INT) {
                jit_emit_branch_not_int32(asm, reg, lbl_slow);
                jit_emit_signext32(asm, reg, reg);
        } else if (class_id == CLASS_FLOAT) {
                jit_emit_branch_not_double(asm, reg, lbl_slow);
                jit_emit_load_imm(asm, BC_S0, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
                jit_emit_sub(asm, reg, reg, BC_S0);
        } else {
                int lbl_true = bc_next_label(ctx), lbl_bool_done = bc_next_label(ctx);
                jit_emit_cmp_ri(asm, reg, NANBOX_VALUE_TRUE);
                jit_emit_branch_eq(asm, lbl_true);
                jit_emit_cmp_ri(asm, reg, NANBOX_VALUE_FALSE);
                jit_emit_branch_ne(asm, lbl_slow);
                jit_emit_load_imm(asm, reg, 0);
                jit_emit_jump(asm, lbl_bool_done);
                jit_emit_label(asm, lbl_true);
                jit_emit_load_imm(asm, reg, 1);
                jit_emit_label(asm, lbl_bool_done);
        }
        jit_emit_load_imm(asm, BC_S0, (i64)1 << slot);
        jit_emit_or(asm, BC_CACHE_MASK, BC_CACHE_MASK, BC_S0);
        jit_emit_label(asm, lbl_ready);
        ctx->raw_dirty |= (u8)1 << slot;
        return reg;
}

inline static void
idbg(JitCtx *ctx, char const *op)
{
        jit_emit_mov(&ctx->asm, BC_A0, BC_TY);
        jit_emit_load_imm(&ctx->asm, BC_A1, ctx->sp);
        jit_emit_load_imm(&ctx->asm, BC_A2, ((iptr)op));
        jit_emit_load_imm(&ctx->asm, BC_CALL, (iptr)jit_rt_idbg);
        bc_emit_runtime_call(ctx, BC_CALL);
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
        bc_emit_runtime_call(ctx, BC_CALL);
}

// ============================================================================
// ============================================================================
// Bytecode pre-scan: discover jump targets and check supportedness
// ============================================================================

static bool
bc_is_pure_bool_predicate(char const *code, int size)
{
        char const *ip = code, *end = code + size;
        while (ip < end) {
                u8 op = (u8)*ip++;
                switch (op) {
                case INSTR_SELF_MEMBER_ACCESS:
                        if (ip + sizeof(i32) > end) return false;
                        ip += sizeof(i32);
                        break;
                case INSTR_NOT:
                case INSTR_RETURN:
                        break;
                case INSTR_JUMP_AND:
                case INSTR_JUMP_OR:
                        if (ip + sizeof(i32) > end) return false;
                        ip += sizeof(i32);
                        break;
                default:
                        return false;
                }
        }
        return ip == end;
}

static bool
bc_prescan(JitCtx *ctx, char const *code, int code_size)
{
        Ty *ty = ctx->ty;
        (void)ty;

        char const *ip = code;
        char const *end = code + code_size;
        /* Tail calls loop to bytecode offset zero; create the label before the
         * emission walk reaches that offset so it is actually bound there. */
        (void)bc_label_for(ctx, 0);

        bool has_try = false;
        bool has_yield = false;
        bool has_yield_some = false;
        bool has_yield_none = false;
        bool has_class = false;
        bool has_call = false;

#define BC_READ(var)  do { __builtin_memcpy(&var, ip, sizeof var); ip += sizeof var; } while (0)
#define BC_SKIP(type) (ip += sizeof(type))
#define BC_SKIPSTR()  (ip += strlen(ip) + 1)

        while (ip < end) {
                char const *instr_start = ip;
                int instr_off = (int)(ip - code);
                (void)instr_start;
                (void)instr_off;

                u8 op = (u8)*ip++;

                /* Only admit instructions whose emitter has been converted to
                 * one-word nanboxed Values.  Unsupported functions continue in
                 * the interpreter rather than executing legacy field offsets. */
                switch (op) {
                case INSTR_NOP:
                case INSTR_BAD_MATCH:
                case INSTR_LOOP_CHECK:
                case INSTR_LOOP_ITER:
                case INSTR_PUSH_INDEX:
                case INSTR_LOAD_LOCAL:
                case INSTR_LOAD_GLOBAL:
                case INSTR_LOAD_THREAD_LOCAL:
                case INSTR_TARGET_CAPTURED:
                case INSTR_LOAD_CAPTURED:
                case INSTR_ASSIGN_LOCAL:
                case INSTR_TARGET_LOCAL:
                case INSTR_ASSIGN:
                case INSTR_POST_DEC:
                case INSTR_ENSURE_LEN_TUPLE:
                case INSTR_INDEX_TUPLE:
                case INSTR_YIELD_SOME:
                case INSTR_INC:
                case INSTR_JUMP_AND:
                case INSTR_JUMP_IF_NIL:
                case INSTR_ASSIGN_SUBSCRIPT:
                case INSTR_ARRAY:
                case INSTR_TUPLE:
                case INSTR_TARGET_SELF_MEMBER:
                case INSTR_TARGET_MEMBER:
                case INSTR_SELF_MEMBER_ACCESS:
                case INSTR_MUT_SUB:
                case INSTR_COUNT:
                case INSTR_CLASS:
                case INSTR_FUNCTION:
                case INSTR_CAPTURE:
                case INSTR_PATCH_ENV:
                case INSTR_MATCH_TAG:
                case INSTR_TRY_ASSIGN_NON_NIL:
                case INSTR_TAG_PUSH:
                case INSTR_CALL_SELF_METHOD:
                case INSTR_CALL_METHOD:
                case INSTR_PUSH_TUPLE_ELEM:
                case INSTR_MEMBER_ACCESS:
                case INSTR_MUT_ADD:
                case INSTR_TARGET_SUBSCRIPT:
                case INSTR_SUBSCRIPT:
                case INSTR_ARRAY_COMPR:
                case INSTR_ARRAY0:
                case INSTR_SAVE_STACK_POS:
                case INSTR_POP_STACK_POS:
                case INSTR_POP_STACK_POS_POP:
                case INSTR_TRY_TAG_POP:
                case INSTR_POP:
                case INSTR_POP2:
                case INSTR_DUP:
                case INSTR_SWAP:
                case INSTR_DUP2_SWAP:
                case INSTR_INT8:
                case INSTR_INTEGER:
                case INSTR_TRUE:
                case INSTR_FALSE:
                case INSTR_NIL:
                case INSTR_REAL:
                case INSTR_NEG:
                case INSTR_NOT:
                case INSTR_EQ:
                case INSTR_NEQ:
                case INSTR_LT:
                case INSTR_GT:
                case INSTR_LEQ:
                case INSTR_GEQ:
                case INSTR_ADD:
                case INSTR_SUB:
                case INSTR_MUL:
                case INSTR_DIV:
                case INSTR_MOD:
                case INSTR_BIT_AND:
                case INSTR_BIT_OR:
                case INSTR_BIT_XOR:
                case INSTR_SHL:
                case INSTR_SHR:
                case INSTR_JUMP:
                case INSTR_JUMP_IF:
                case INSTR_JUMP_IF_NOT:
                case INSTR_JEQ:
                case INSTR_JNE:
                case INSTR_JLT:
                case INSTR_JGT:
                case INSTR_JLE:
                case INSTR_JGE:
                case INSTR_TAIL_CALL:
                case INSTR_RETURN:
                case INSTR_RETURN_PRESERVE_CTX:
                case INSTR_HALT:
                        break;
                case INSTR_CALL_GLOBAL:
                        break;
                case INSTR_CALL:
                        break;
                case INSTR_MUT_DIV:
                case INSTR_JUMP_OR:
                        break;
                default:
#if JIT_SCAN_LOG
                        LOGX("JIT: whitelist bail on %s at offset %d", GetInstructionName(op), instr_off);
#endif
                        return false;
                }

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
                case INSTR_TAIL_CALL:
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
                case INSTR_POST_INC:
                case INSTR_POST_DEC:
                case INSTR_PRE_INC:
                case INSTR_PRE_DEC:
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
                case INSTR_RETHROW:
                case INSTR_CATCH:
                case INSTR_FINALLY:
                case INSTR_END_TRY:
                case INSTR_NONE:
                case INSTR_SENTINEL:
                case INSTR_RETURN_IF_NOT_NONE:
                case INSTR_TO_STRING:
                case INSTR_SLICE:
                        break;

                case INSTR_PATCH_ENV:
                        BC_READ(n);
                        break;

                case INSTR_TRY: {
                        has_try = true;

                        int catch_off, finally_off, end_off;

                        BC_READ(catch_off);
                        int catch_target = (int)(ip - code) + catch_off;
                        if (bc_label_for(ctx, catch_target) < 0) return false;

                        BC_READ(finally_off);
                        if (finally_off != -1) {
                                int finally_target = (int)(ip - code) + finally_off;
                                if (bc_label_for(ctx, finally_target) < 0) return false;
                        }

                        BC_READ(end_off);
                        if (end_off != -1) {
                                int end_target = (int)(ip - code) + end_off;
                                if (bc_label_for(ctx, end_target) < 0) return false;
                        }

                        break;
                }

                case INSTR_YIELD:
                case INSTR_YIELD_SOME:
                        /* A yielded value can receive a value on resume.  The
                         * compiled suspension path is currently safe only when
                         * that resume value is immediately discarded. */
                        if (ip >= end || (u8)*ip != INSTR_POP) return false;
                        has_yield = true;
                        has_yield_some = true;
                        break;
                case INSTR_YIELD_NONE:
                        has_yield = true;
                        has_yield_none = true;
                        break;

                case INSTR_LOAD_LOCAL:
                        BC_READ(n);
                        if (n >= 0 && n < ctx->bound) {
                                ctx->raw_scores[n] += 3;
                        }
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        break;

                case INSTR_LOAD_REF:
                case INSTR_LOAD_CAPTURED:
                        BC_SKIP(i32);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        break;

                case INSTR_ASSIGN_LOCAL:
                case INSTR_TARGET_LOCAL:
                        BC_READ(n);
                        if (n >= 0 && n < ctx->bound) {
                                ctx->raw_scores[n] += op == INSTR_TARGET_LOCAL ? 8 : 4;
                        }
                        break;

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
                case INSTR_TRY_MEMBER_ACCESS:
                case INSTR_SELF_MEMBER_ACCESS:
                        BC_SKIP(i32);
                        break;

                case INSTR_TARGET_MEMBER:
                case INSTR_TARGET_SELF_MEMBER:
                        BC_SKIP(i32);
                        break;

                case INSTR_GET_MEMBER:
                        break;

                case INSTR_TARGET_DYN_MEMBER:
                        return false;

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
                        has_call = true;
                        BC_SKIP(i32);  // n (argc)
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;

                case INSTR_CALL_METHOD:
                case INSTR_CALL_SELF_METHOD: {
                        int member;
                        BC_SKIP(i32);  // n (argc)
                        BC_READ(member);
                        if (member < 0) return false;
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;
                }

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

                case INSTR_TAG_PUSH:
                        BC_SKIP(i32);
                        break;

                case INSTR_TRY_TAG_POP: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // tag
                        break;
                }

                case INSTR_ASSIGN_SUBSCRIPT:
                        BC_SKIP(u8);
                        break;

                case INSTR_HALT:
                        break;

                case INSTR_TAG:
                case INSTR_CLASS:
                        has_class = true;
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

                case INSTR_PUSH_ARRAY_ELEM:
                        BC_SKIP(i32);
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

                case INSTR_TRY_REGEX: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(iptr); // regex pointer
                        break;
                }

                case INSTR_ASSIGN_REGEX_MATCHES:
                        BC_SKIP(i32); // n
                        break;

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

                case INSTR_ARRAY_REST: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // start index
                        BC_SKIP(i32); // suffix count
                        break;
                }

                case INSTR_TUPLE_REST: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        BC_SKIP(i32); // start index
                        break;
                }

                case INSTR_RECORD_REST: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        // Skip alignment padding + i32 list terminated by -1
                        ip = ALIGNED_FOR(i32, ip);
                        while (*(i32 const *)ip != -1) ip += sizeof (i32);
                        ip += sizeof (i32); // skip the -1 sentinel
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

                case INSTR_FUNCTION:
                case INSTR_GENERATOR: {
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

                BcCfgNode *node = &ctx->cfg_nodes[ctx->cfg_count++];
                node->offset = instr_off;
                node->next = (int)(ip - code);
                node->target = -1;
                node->op = op;
                switch (op) {
                case INSTR_JUMP:
                case INSTR_JUMP_IF:
                case INSTR_JUMP_IF_NOT:
                case INSTR_JUMP_IF_NIL:
                case INSTR_JUMP_IF_NONE:
                case INSTR_JUMP_AND:
                case INSTR_JUMP_OR:
                case INSTR_JUMP_WTF:
                case INSTR_JEQ:
                case INSTR_JNE:
                case INSTR_JLT:
                case INSTR_JGT:
                case INSTR_JLE:
                case INSTR_JGE: {
                        i32 rel;
                        __builtin_memcpy(&rel, code + instr_off + 1, sizeof rel);
                        node->target = node->next + rel;
                        break;
                }
                default:
                        break;
                }
        }

#undef BC_READ
#undef BC_SKIP
#undef BC_SKIPSTR

        // Can't use setjmp-based try blocks in generators: yield suspends
        // the coroutine, invalidating the setjmp frame.
        if ((has_try && has_yield) || (has_yield_some && has_yield_none)
) {
                return false;
        }
        ctx->cfg_has_try = has_try;
        ctx->cfg_has_yield = has_yield;
        return true;
}

// ============================================================================
// Runtime helpers for bytecode JIT (called from native code)
// ============================================================================

static void
jit_rt_call(Ty *ty, Value *result, Value *fn, int argc)
{
        Value _fn = *fn;
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + argc;
        DoCallEx(ty, &_fn, argc, &NIL, true);
}

// Trampoline-aware call helper.
// Returns 0 if the call was handled synchronously (non-JIT or interpreted).
// Returns 1 if the callee is JIT-compiled and the trampoline should dispatch it.

static int
jit_rt_call_trampoline(Ty *ty, Value *out, Value *fn, int argc)
{
        Value _fn = *fn;

        vN(STACK) = (out + argc) - vv(STACK);

        JitFn *jit;

        if (
                (V_TYPE(_fn) != VALUE_FUNCTION && V_TYPE(_fn) != VALUE_BOUND_FUNCTION)
             || is_starred(&_fn)
             || ((jit = try_jit(ty, &_fn)) == NULL)
        ) {
                DoCallEx(ty, &_fn, argc, &NIL, true);
                return 0;
        }

        // Callee is JIT-compiled: set up its frame and signal the trampoline
        vm_xcall(ty, &_fn, NULL, argc, NULL);

        ty->ip = &JIT;

        return 1;
}

// Fast frame setup for simple functions (no rest args, no kwargs).
// Replaces the expensive xcall() path for known-simple functions.
static inline void
jit_fast_frame(Ty *ty, Value const *fn, Value const *self, int argc)
{
        if (UNLIKELY(vN(ty->st->frames) >= TY_MAX_CALL_DEPTH)) {
                zP("maximum call depth exceeded");
        }
        int bound = V_INFO(*(fn))[FUN_INFO_BOUND];
        int fp = vN(STACK) - argc;

        // Ensure stack capacity
        int needed = fp + bound;
        if (UNLIKELY((usize)needed > vC(STACK))) {
                xvR(STACK, needed + 256);
        }

        Value *base = vv(STACK) + fp;
        if (argc < bound) {
                for (int i = argc; i < bound; ++i) {
                        base[i] = NIL;
                }
        }
        vN(STACK) = needed;

        // Set self for methods
        if (self != NULL) {
                int np = V_INFO(*(fn))[FUN_INFO_PARAM_COUNT];
                base[np] = *self;
        }

        // Push frame and call return address
        xvP(ty->st->frames, ((Frame){ .fp = fp, .f = *fn, .ip = ty->ip }));
        xvP(ty->st->calls, ty->ip);

        ty->ip = &JIT;

        CO_LOG("jit_fast_frame", TERM(33;1), "");
}

// Run a JIT function through an inline trampoline loop.
// Handles nested JIT-to-JIT calls without returning to the outer trampoline.
static inline void
jit_run_trampoline(Ty *ty, JitFn *jit, Value **env)
{
        CO_LOG("jit_run_trampoline", TERM(32;1), "enter");

        vm_trampoline_linked(ty, jit, env);

        CO_LOG("jit_run_trampoline", TERM(31;1), "ret");
}

// ret 1 for handled, 0 for fallback
static int
jit_rt_baked_call(Ty *ty, Value *self, Value *fn, int class_id, int argc)
{
        if (UNLIKELY(ClassOf(self) != class_id)) {
                return 0;
        }

        if (rest_idx_of(fn) >= 0 || kwargs_idx_of(fn) >= 0 || is_starred(fn)) {
                return 0;
        }

        JitFn *jit = try_jit(ty, fn);
        if (UNLIKELY(jit == NULL)) {
                return 0;
        }

        Value _self = *self;

        STAT(call_method_baked);

        Value *items = vv(ty->st->stack);
        jit_fast_frame(ty, fn, &_self, argc);
        jit_run_trampoline(ty, jit, V_ENV(*(fn)));

        return 1 + (items != vv(ty->st->stack));
}

static bool
jit_linkable_function(Value const *fn, int argc)
{
        return V_TYPE(*(fn)) == VALUE_FUNCTION
            && argc == param_count_of(fn)
            && rest_idx_of(fn) == -1
            && kwargs_idx_of(fn) == -1
            && !is_starred(fn)
            && !is_overload(fn);
}


static int
jit_rt_fast_self_call(Ty *ty, Value *out, Value *fn, int argc)
{
        FrameStack *frames = vm_get_frames(ty);
        if (vN(*frames) == 0) return 0;
        Value callee = vvL(*frames)->f;
        if (fn->bits.as_int64 != callee.bits.as_int64 || argc != param_count_of(&callee))
                return 0;
        JitFn *jit = jit_of(&callee);
        if (jit == NULL) return 0;
        Value *items = vv(STACK);
        vN(STACK) = (out + argc) - vv(STACK);
        jit_fast_frame(ty, &callee, NULL, argc);
        vm_trampoline_linked(ty, jit, V_ENV(callee));
        return 1 + (items != vv(STACK));
}

static int
jit_rt_fast_self_tail(Ty *ty, Value *args, Value *fn, int argc)
{
        FrameStack *frames = vm_get_frames(ty);
        if (vN(*frames) == 0 || fn->bits.as_int64 != vvL(*frames)->f.bits.as_int64)
                return 0;
        Frame *frame = vvL(*frames);
        Value callee = frame->f;
        if (!jit_linkable_function(&callee, argc)) return 0;
        int bound = V_INFO(callee)[FUN_INFO_BOUND];
        Value *base = v_(STACK, frame->fp);
        memmove(base, args, argc * sizeof (Value));
        for (int i = argc; i < bound; ++i) base[i] = NIL;
        vN(STACK) = frame->fp + bound;
        return 1;
}


static bool
jit_linkable_global(Value const *fn, int argc)
{
        return jit_linkable_function(fn, argc) && class_of(fn) == -1;
}

static int
jit_rt_linked_global_call(Ty *ty, int gi, int argc, JitFn *expected)
{
        Value *fn = vm_global(ty, gi);
        if (V_TYPE(*(fn)) != VALUE_FUNCTION || jit_of(fn) != expected) {
                return 0;
        }
        Value *items = vv(ty->st->stack);
        jit_fast_frame(ty, fn, NULL, argc);
        vm_trampoline_linked(ty, expected, V_ENV(*(fn)));
        return 1 + (items != vv(ty->st->stack));
}

// ret 1 for handled, 0 for fallback
static int
jit_rt_fast_global_call(Ty *ty, int gi, int argc)
{
        Value *fn = vm_global(ty, gi);

        if (
                (V_TYPE(*(fn)) != VALUE_FUNCTION && V_TYPE(*(fn)) != VALUE_BOUND_FUNCTION)
             || (rest_idx_of(fn)   >= 0)
             || (kwargs_idx_of(fn) >= 0)
             || is_starred(fn)
        ){
                return 0;
        }

        JitFn *jit = try_jit(ty, fn);
        if (jit == NULL) {
                return 0;
        }

        CO_LOG("jit_rt_fast_global_call", TERM(32;1), "global %d", gi);

        Value *items = vv(ty->st->stack);
        jit_fast_frame(ty, fn, NULL, argc);
        jit_run_trampoline(ty, jit, V_ENV(*(fn)));

        return 1 + (items != vv(ty->st->stack));
}

static void
jit_rt_call_method(Ty *ty, Value *result, Value *self, int member_id, int argc)
{
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + argc;
        if (self == NULL) {
                self = vm_get_self(ty);
        }
        xvP(STACK, *self);
        CallMethod(ty, member_id, argc, 0, true, true);
        CO_LOG("jit_rt_call", TERM(32;1), "");
}

// Call a method directly with a baked Value* (fast path when class is known at JIT time)
static void
jit_rt_call_method_direct(Ty *ty, Value *result, Value *self, Value *method, int argc)
{
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + argc;
        Value val = vm_call_method(ty, self, method, argc);
        *v_(STACK, idx) = val;
        CO_LOG("jit_rt_call_method_direct", TERM(32;1), "");
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

        CO_LOG("jit_rt_call_self_method_guarded", TERM(32;1), "class_id %d member_id %d", class_id, member_id);

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
        int expected_type = (int)(vtype_and_member >> 32);
        int member_id  = (int)(vtype_and_member);

        if (self == NULL) {
                self = vm_get_self(ty);
        }

        Value _self = *self;

        CO_LOG("jit_rt_call_builtin_method", TERM(32;1), "type %d member %d", expected_type, member_id);

        if (LIKELY(V_TYPE(*self) == expected_type)) {
                STAT(call_method_builtin);
                ptrdiff_t idx = (result - vv(STACK));
                vN(STACK) = idx + argc;
                gP(&_self);
                Value val = (*func)(ty, &_self, argc, NULL);
                vN(STACK) = idx + 1;
                v_L(STACK) = val;
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
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + argc;
        Value val = func(ty, argc, NULL);
        vN(STACK) = idx + 1;
        v_L(STACK) = val;
        vm_check_flags(ty);
}

static int
jit_rt_get_fp(Ty *ty)
{
        return vvL(ty->st->frames)->fp;
}

static int
jit_rt_yield(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        DoYield(ty);
        return vvL(ty->st->frames)->fp;
}

static int
jit_rt_yield_some(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        v_L(STACK) = Some(v_L(STACK));
        DoYield(ty);
        return vvL(ty->st->frames)->fp;
}

static int
jit_rt_yield_none(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        xvP(STACK, None);
        DoYield(ty);
        return vvL(ty->st->frames)->fp;
}

static void
jit_rt_check_match(Ty *ty, Value *result, Value *value, Value *pattern)
{
        vN(STACK) = result - vv(STACK) + 2;
        DoCheckMatch(ty, true);
}

static int
jit_rt_compare(Ty *ty, Value *a, Value *b)
{
        /* An overloaded <=> re-enters the VM and pushes at vN(STACK). */
        ptrdiff_t ia = a - vv(STACK);
        ptrdiff_t ib = b - vv(STACK);
        vN(STACK) = max(ia, ib) + 1;
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
        *result = STRING(ty, str, total);
}

// ============================================================================
// Bytecode emission
// ============================================================================

static Class *expected_class_of(Ty *ty, Type const *t);

static void
bc_copy_value(JitCtx *ctx, int dst_reg, int dst_off, int src_reg, int src_off)
{
        dasm_State **asm = &ctx->asm;
        /* Immediate int/bool-heavy code only consumes 32 payload bits.  A
         * full word is still required for arbitrary Values, so retain the
         * canonical one-word copy. */
        jit_emit_ldr64(asm, BC_S0, src_reg, src_off);
        jit_emit_str64(asm, BC_S0, dst_reg, dst_off);
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
        int lbl_not_ref = bc_next_label(ctx);
        jit_emit_add_imm(asm, dst, src, src_off);
        jit_emit_ldr64(asm, BC_S0, dst, 0);
        jit_emit_branch_not_pointer(asm, BC_S0, lbl_skip);
        jit_emit_ldrb(asm, BC_S1, BC_S0, offsetof(ValueBox, payload.type));
        jit_emit_cmp_ri(asm, BC_S1, VALUE_REF);
        jit_emit_branch_ne(asm, lbl_not_ref);
        jit_emit_ldr64(asm, dst, BC_S0, offsetof(ValueBox, payload.ref));
        jit_emit_jump(asm, lbl_skip);
        jit_emit_label(asm, lbl_not_ref);
        jit_emit_add_imm(asm, dst, src, src_off);
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
        bc_emit_runtime_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_no_irq);
}

static void
bc_push_bits(JitCtx *ctx, u64 bits, Type *type)
{
        dasm_State **asm = &ctx->asm;
        jit_emit_load_imm(asm, BC_S0, (iptr)bits);
        jit_emit_str64(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp));
        ctx->op_types[ctx->sp++] = type;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
}

static void
bc_push_integer(JitCtx *ctx, intmax_t val)
{
        Value v = value_integer(ctx->ty, val);
        if (nanbox_is_pointer(v.bits)) gc_immortalize(ctx->ty, &v);
        bc_push_bits(ctx, v.bits.as_int64, INT_TYPE);
}

static void
bc_push_bool(JitCtx *ctx, bool val)
{
        bc_push_bits(ctx, nanbox_from_boolean(val).as_int64, BOOL_TYPE);
}

static void
bc_push_nil(JitCtx *ctx)
{
        bc_push_bits(ctx, nanbox_null().as_int64, NIL_TYPE);
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
        bc_emit_reentrant_call(ctx, BC_CALL);

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
        bc_emit_reentrant_call(ctx, BC_CALL);
}

static void
bc_decode_int32(JitCtx *ctx, int word_reg, int dst_reg)
{
        jit_emit_signext32(&ctx->asm, dst_reg, word_reg);
}

static void
bc_encode_int32(JitCtx *ctx, int value_reg, int dst_reg)
{
        dasm_State **asm = &ctx->asm;
        jit_emit_mov32(asm, dst_reg, value_reg);
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_MIN_NUMBER);
        jit_emit_or(asm, dst_reg, dst_reg, BC_S2);
}

static void *
bc_mut_runtime(u8 op)
{
        return op == INSTR_MUT_ADD ? (void *)jit_rt_mut_add
             : op == INSTR_MUT_SUB ? (void *)jit_rt_mut_sub
             : op == INSTR_MUT_MUL ? (void *)jit_rt_mut_mul
             : op == INSTR_MUT_DIV ? (void *)jit_rt_mut_div
             : op == INSTR_MUT_MOD ? (void *)jit_rt_mut_mod
             : NULL;
}

static int
bc_emit_int_local_operand(JitCtx *ctx, int local, int scratch, int lbl_slow)
{
        dasm_State **asm = &ctx->asm;
        jit_emit_ldr64(asm, scratch, BC_LOC, local * VALUE_SIZE);
        jit_emit_branch_not_int32(asm, scratch, lbl_slow);
        bc_decode_int32(ctx, scratch, scratch);
        return scratch;
}

static void
bc_emit_int_local_jcmp(JitCtx *ctx, int left, int right, imax immediate,
                       u8 op, int lbl_target)
{
        dasm_State **asm = &ctx->asm;
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);
        int left_reg = bc_emit_int_local_operand(
                ctx, left, BC_S0, lbl_slow
        );
        int right_reg = right >= 0
                ? bc_emit_int_local_operand(ctx, right, BC_S1, lbl_slow)
                : BC_S1;
        EMIT_STAT(jit_rt_stat_jcmp_int);
        if (right < 0) {
                jit_emit_load_imm(asm, right_reg, immediate);
        }
        jit_emit_cmp_rr(asm, left_reg, right_reg);
        switch (op) {
        case INSTR_JLT: jit_emit_branch_lt(asm, lbl_target); break;
        case INSTR_JGT: jit_emit_branch_gt(asm, lbl_target); break;
        case INSTR_JLE: jit_emit_branch_le(asm, lbl_target); break;
        case INSTR_JGE: jit_emit_branch_ge(asm, lbl_target); break;
        }
        jit_emit_jump(asm, lbl_done);

        jit_emit_label(asm, lbl_slow);
        int left_off = OP_OFF(ctx->sp);
        int right_off = OP_OFF(ctx->sp + 1);
        bc_copy_value(
                ctx, BC_OPS, left_off, BC_LOC, left * VALUE_SIZE
        );
        if (right >= 0) {
                bc_copy_value(
                        ctx, BC_OPS, right_off, BC_LOC, right * VALUE_SIZE
                );
        } else {
                Value iv = value_integer(ctx->ty, immediate);
                if (nanbox_is_pointer(iv.bits)) gc_immortalize(ctx->ty, &iv);
                jit_emit_load_imm(asm, BC_S0, iv.bits.as_int64);
                jit_emit_str64(asm, BC_S0, BC_OPS, right_off);
        }
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, left_off);
        jit_emit_add_imm(asm, BC_A2, BC_OPS, right_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_compare);
        bc_emit_runtime_call(ctx, BC_CALL);
        /* Reload clobbers BC_RET on x64, but preserves comparison flags. */
        jit_emit_cmp_ri32(asm, BC_RET, 0);
        jit_emit_reload_stack(asm, ctx->bound);
        switch (op) {
        case INSTR_JLT: jit_emit_branch_lt(asm, lbl_target); break;
        case INSTR_JGT: jit_emit_branch_gt(asm, lbl_target); break;
        case INSTR_JLE: jit_emit_branch_le(asm, lbl_target); break;
        case INSTR_JGE: jit_emit_branch_ge(asm, lbl_target); break;
        }
        jit_emit_label(asm, lbl_done);
}

static bool
bc_try_local_array_swap(JitCtx *ctx, char const *code, char const *end,
                        char const **ip, Symbol **locals, int load_off, int array_local)
{
        (void)locals;
        char const *q = *ip;
#define READ_LOCAL(dst) do { \
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL || q + sizeof(int) > end) return false; \
        __builtin_memcpy(&(dst), q, sizeof(int)); q += sizeof(int); \
        if (!defined_TY_NO_LOG_placeholder) {} \
} while (0)
        /* Parse manually because debug bytecode includes local names. */
        int i, tmp, array2, j, array3, i2, tmp2, array4, j2;
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false;
        __builtin_memcpy(&i, q, sizeof i); q += sizeof i;
#ifndef TY_NO_LOG
        q += strlen(q) + 1;
#endif
        if (q >= end || (u8)*q++ != INSTR_SUBSCRIPT) return false;
        if (q >= end || (u8)*q++ != INSTR_ASSIGN_LOCAL) return false;
        __builtin_memcpy(&tmp, q, sizeof tmp); q += sizeof tmp;
#ifndef TY_NO_LOG
        q += strlen(q) + 1;
#endif
#define PARSE_LOCAL(dst) do { if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false; \
        __builtin_memcpy(&(dst), q, sizeof(dst)); q += sizeof(dst); \
        /* names follow operands in logging builds */ \
        q += 0; } while (0)
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false;
        __builtin_memcpy(&array2,q,sizeof array2); q+=sizeof array2;
#ifndef TY_NO_LOG
        q += strlen(q)+1;
#endif
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false;
        __builtin_memcpy(&j,q,sizeof j); q+=sizeof j;
#ifndef TY_NO_LOG
        q += strlen(q)+1;
#endif
        if (q >= end || (u8)*q++ != INSTR_SUBSCRIPT) return false;
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false;
        __builtin_memcpy(&array3,q,sizeof array3); q+=sizeof array3;
#ifndef TY_NO_LOG
        q += strlen(q)+1;
#endif
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false;
        __builtin_memcpy(&i2,q,sizeof i2); q+=sizeof i2;
#ifndef TY_NO_LOG
        q += strlen(q)+1;
#endif
        if (q + 2 > end || (u8)*q++ != INSTR_ASSIGN_SUBSCRIPT || (u8)*q++ != 1) return false;
        if (q >= end || (u8)*q++ != INSTR_POP) return false;
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false;
        __builtin_memcpy(&tmp2,q,sizeof tmp2); q+=sizeof tmp2;
#ifndef TY_NO_LOG
        q += strlen(q)+1;
#endif
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false;
        __builtin_memcpy(&array4,q,sizeof array4); q+=sizeof array4;
#ifndef TY_NO_LOG
        q += strlen(q)+1;
#endif
        if (q >= end || (u8)*q++ != INSTR_LOAD_LOCAL) return false;
        __builtin_memcpy(&j2,q,sizeof j2); q+=sizeof j2;
#ifndef TY_NO_LOG
        q += strlen(q)+1;
#endif
        if (q + 2 > end || (u8)*q++ != INSTR_ASSIGN_SUBSCRIPT || (u8)*q++ != 1) return false;
        if (q >= end || (u8)*q++ != INSTR_POP) return false;
        /* Fold the canonical i += 1; j -= 1 tail as well. */
        char const *after_swap = q;
        bool fold_cursors = false;
        if (q + 2 < end && (u8)q[0] == INSTR_INT8 && (i8)q[1] == 1) {
                q += 2;
                int ti, tj;
                if (q < end && (u8)*q++ == INSTR_TARGET_LOCAL) {
                        __builtin_memcpy(&ti,q,sizeof ti); q+=sizeof ti;
#ifndef TY_NO_LOG
                        q += strlen(q)+1;
#endif
                        if (q + 2 < end && (u8)*q++ == INSTR_MUT_ADD && (u8)*q++ == INSTR_POP
                            && (u8)*q++ == INSTR_INT8 && (i8)*q++ == 1
                            && q < end && (u8)*q++ == INSTR_TARGET_LOCAL) {
                                __builtin_memcpy(&tj,q,sizeof tj); q+=sizeof tj;
#ifndef TY_NO_LOG
                                q += strlen(q)+1;
#endif
                                if (q + 2 <= end && (u8)*q++ == INSTR_MUT_SUB && (u8)*q++ == INSTR_POP
                                    && ti == i && tj == j) fold_cursors = true;
                        }
                }
        }
        if (!fold_cursors) q = after_swap;
        if (array2 != array_local || array3 != array_local || array4 != array_local
            || i2 != i || j2 != j || tmp2 != tmp) return false;
        if (i < 0 || i >= ctx->bound || j < 0 || j >= ctx->bound) return false;
        for (char const *z = *ip; z < q; ++z) if (bc_find_label(ctx, (int)(z-code)) >= 0) return false;
        dasm_State **asm=&ctx->asm; int lbl_slow=bc_next_label(ctx),lbl_done=bc_next_label(ctx);
        int ao=array_local*VALUE_SIZE,io=i*VALUE_SIZE,jo=j*VALUE_SIZE;
        jit_emit_ldr64(asm,BC_S3,BC_LOC,ao); jit_emit_decode_direct_array(asm,BC_S1,BC_S3,lbl_slow);
        jit_emit_ldr64(asm,BC_S0,BC_LOC,io); jit_emit_branch_not_int32(asm,BC_S0,lbl_slow); bc_decode_int32(ctx,BC_S0,BC_S0);
        jit_emit_ldr64(asm,BC_S3,BC_LOC,jo); jit_emit_branch_not_int32(asm,BC_S3,lbl_slow); bc_decode_int32(ctx,BC_S3,BC_S3);
        jit_emit_ldr64(asm,BC_S2,BC_S1,offsetof(Array,count));
        jit_emit_cmp_ri(asm,BC_S0,0); jit_emit_branch_lt(asm,lbl_slow); jit_emit_cmp_rr(asm,BC_S0,BC_S2); jit_emit_branch_ge(asm,lbl_slow);
        jit_emit_cmp_ri(asm,BC_S3,0); jit_emit_branch_lt(asm,lbl_slow); jit_emit_cmp_rr(asm,BC_S3,BC_S2); jit_emit_branch_ge(asm,lbl_slow);
        jit_emit_ldr64(asm,BC_S1,BC_S1,offsetof(Array,items));
        jit_emit_ldr64_index8(asm,BC_S2,BC_S1,BC_S0); jit_emit_ldr64_index8(asm,BC_CALL,BC_S1,BC_S3);
        jit_emit_str64_index8(asm,BC_CALL,BC_S1,BC_S0); jit_emit_str64_index8(asm,BC_S2,BC_S1,BC_S3);
        if (fold_cursors) {
                jit_emit_add_imm(asm, BC_S0, BC_S0, 1);
                jit_emit_add_imm(asm, BC_S3, BC_S3, -1);
                bc_encode_int32(ctx, BC_S0, BC_S0); bc_encode_int32(ctx, BC_S3, BC_S3);
                jit_emit_str64(asm, BC_S0, BC_LOC, io); jit_emit_str64(asm, BC_S3, BC_LOC, jo);
        }
        jit_emit_jump(asm,lbl_done);
        jit_emit_label(asm,lbl_slow);
        jit_emit_mov(asm,BC_A0,BC_TY); jit_emit_add_imm(asm,BC_A1,BC_LOC,ao); jit_emit_add_imm(asm,BC_A2,BC_LOC,io); jit_emit_add_imm(asm,BC_A3,BC_LOC,jo);
        jit_emit_load_imm(asm,BC_CALL,(iptr)jit_rt_swap_subscripts); bc_emit_reentrant_call(ctx,BC_CALL);
        if (fold_cursors) {
                Value one = value_integer(ctx->ty, 1);
                jit_emit_load_imm(asm, BC_S0, one.bits.as_int64); jit_emit_str64(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp));
                jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_LOC, io); jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp)); jit_emit_mov(asm, BC_A3, BC_A2);
                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_mut_add); bc_emit_reentrant_call(ctx,BC_CALL);
                jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_LOC, jo); jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp)); jit_emit_mov(asm, BC_A3, BC_A2);
                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_mut_sub); bc_emit_reentrant_call(ctx,BC_CALL);
        }
        jit_emit_label(asm,lbl_done); *ip=q; return true;
#undef READ_LOCAL
#undef PARSE_LOCAL
}

static bool
bc_try_local_array_get_assign(JitCtx *ctx, char const *code, char const *end,
                              char const **ip, Symbol **locals,
                              int load_off, int array_local)
{
        if (getenv("TY_JIT_NO_LOCAL_ARRAY_GET_ASSIGN") != NULL
            || array_local < 0 || array_local >= ctx->bound) {
                return false;
        }
        Class *array_class = expected_class_of(
                ctx->ty, locals[array_local]->type
        );
        if (array_class == NULL || array_class->i != CLASS_ARRAY) {
                return false;
        }
        char const *q = *ip;
        if (q >= end) {
                return false;
        }
        int index_off_bc = (int)(q - code);
        int index_local = -1;
        imax immediate = 0;
        if ((u8)*q == INSTR_LOAD_LOCAL) {
                ++q;
                if (q + sizeof index_local > end) {
                        return false;
                }
                __builtin_memcpy(&index_local, q, sizeof index_local);
                q += sizeof index_local;
#ifndef TY_NO_LOG
                q += strlen(q) + 1;
#endif
                if (index_local < 0 || index_local >= ctx->bound) {
                        return false;
                }
                Class *index_class = expected_class_of(
                        ctx->ty, locals[index_local]->type
                );
                if (index_class == NULL || index_class->i != CLASS_INT) {
                        return false;
                }
        } else if ((u8)*q == INSTR_INT8) {
                ++q;
                if (q >= end) {
                        return false;
                }
                immediate = (i8)*q++;
        } else if ((u8)*q == INSTR_INTEGER) {
                ++q;
                if (q + sizeof immediate > end) {
                        return false;
                }
                __builtin_memcpy(&immediate, q, sizeof immediate);
                q += sizeof immediate;
        } else {
                return false;
        }
        int subscript_off = (int)(q - code);
        if (q >= end || (u8)*q++ != INSTR_SUBSCRIPT) {
                return false;
        }
        int assign_off = (int)(q - code);
        if (q + 1 + sizeof(int) > end || (u8)*q++ != INSTR_ASSIGN_LOCAL) {
                return false;
        }
        int destination;
        __builtin_memcpy(&destination, q, sizeof destination);
        q += sizeof destination;
#ifndef TY_NO_LOG
        q += strlen(q) + 1;
#endif
        if (destination < 0 || destination >= ctx->bound
            || bc_find_label(ctx, index_off_bc) >= 0
            || bc_find_label(ctx, subscript_off) >= 0
            || bc_find_label(ctx, assign_off) >= 0
            || !bc_cfg_same_block(
                    ctx, load_off, index_off_bc, subscript_off
               )
            || !bc_cfg_same_block(
                    ctx, subscript_off, assign_off, assign_off
               )) {
                return false;
        }
#ifdef TY_PROFILER
        bc_emit_profiler_tick_at(ctx, code + index_off_bc);
        bc_emit_profiler_tick_at(ctx, code + subscript_off);
        bc_emit_profiler_tick_at(ctx, code + assign_off);
#endif
        dasm_State **asm = &ctx->asm;
        int array_off = array_local * VALUE_SIZE, destination_off = destination * VALUE_SIZE;
        int result_off = OP_OFF(ctx->sp);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        /* Decode the direct Array tag and pointer. */
        jit_emit_ldr64(asm, BC_S3, BC_LOC, array_off);
        jit_emit_decode_direct_array(asm, BC_S1, BC_S3, lbl_slow);
        if (index_local >= 0) {
                jit_emit_ldr64(asm, BC_S0, BC_LOC, index_local * VALUE_SIZE);
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_HIGH16_TAG);
                jit_emit_and(asm, BC_S3, BC_S0, BC_S2);
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_MIN_NUMBER);
                jit_emit_cmp_rr(asm, BC_S3, BC_S2);
                jit_emit_branch_ne(asm, lbl_slow);
                bc_decode_int32(ctx, BC_S0, BC_S0);
        } else {
                if (immediate < INT32_MIN || immediate > INT32_MAX) return false;
                jit_emit_load_imm(asm, BC_S0, immediate);
        }
        jit_emit_ldr64(asm, BC_S2, BC_S1, offsetof(Array, count));
        int lbl_nonneg = bc_next_label(ctx);
        jit_emit_cmp_ri(asm, BC_S0, 0);
        jit_emit_branch_ge(asm, lbl_nonneg);
        jit_emit_add(asm, BC_S0, BC_S0, BC_S2);
        jit_emit_label(asm, lbl_nonneg);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_lt(asm, lbl_slow);
        jit_emit_cmp_rr(asm, BC_S0, BC_S2); jit_emit_branch_ge(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S1, BC_S1, offsetof(Array, items));
        jit_emit_ldr64_index8(asm, BC_S0, BC_S1, BC_S0);
        jit_emit_str64(asm, BC_S0, BC_LOC, destination_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        bc_copy_value(ctx, BC_OPS, result_off, BC_LOC, array_off);
        int idx_off = OP_OFF(ctx->sp + 1);
        if (index_local >= 0) bc_copy_value(ctx, BC_OPS, idx_off, BC_LOC, index_local * VALUE_SIZE);
        else {
                Value iv = value_integer(ctx->ty, immediate);
                if (nanbox_is_pointer(iv.bits)) gc_immortalize(ctx->ty, &iv);
                jit_emit_load_imm(asm, BC_S0, iv.bits.as_int64);
                jit_emit_str64(asm, BC_S0, BC_OPS, idx_off);
        }
        jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_subscript); bc_emit_reentrant_call(ctx, BC_CALL);
        bc_copy_value(ctx, BC_LOC, destination_off, BC_OPS, result_off);
        jit_emit_label(asm, lbl_done);
        bc_raw_kill(ctx, destination);
        *ip = q;
        return true;
}

static bool
bc_try_local_array_store_pop(JitCtx *ctx, char const *code, char const *end,
                             char const **ip, Symbol **locals,
                             int load_off, int array_local)
{
        if (getenv("TY_JIT_NO_LOCAL_ARRAY_STORE") != NULL
            || ctx->sp < 1 || array_local < 0 || array_local >= ctx->bound) {
                return false;
        }
        Class *array_class = expected_class_of(
                ctx->ty, locals[array_local]->type
        );
        if (array_class == NULL || array_class->i != CLASS_ARRAY) {
                return false;
        }
        char const *q = *ip;
        if (q >= end) {
                return false;
        }
        int index_off_bc = (int)(q - code);
        int index_local = -1;
        imax immediate = 0;
        if ((u8)*q == INSTR_LOAD_LOCAL) {
                ++q;
                if (q + sizeof index_local > end) {
                        return false;
                }
                __builtin_memcpy(&index_local, q, sizeof index_local);
                q += sizeof index_local;
#ifndef TY_NO_LOG
                q += strlen(q) + 1;
#endif
                if (index_local < 0 || index_local >= ctx->bound) {
                        return false;
                }
                Class *index_class = expected_class_of(
                        ctx->ty, locals[index_local]->type
                );
                if (index_class == NULL || index_class->i != CLASS_INT) {
                        return false;
                }
        } else if ((u8)*q == INSTR_INT8) {
                ++q;
                if (q >= end) {
                        return false;
                }
                immediate = (i8)*q++;
        } else if ((u8)*q == INSTR_INTEGER) {
                ++q;
                if (q + sizeof immediate > end) {
                        return false;
                }
                __builtin_memcpy(&immediate, q, sizeof immediate);
                q += sizeof immediate;
        } else {
                return false;
        }
        int assign_off = (int)(q - code);
        if (q + 3 > end || (u8)*q++ != INSTR_ASSIGN_SUBSCRIPT
            || (u8)*q++ != 1) {
                return false;
        }
        int pop_off = (int)(q - code);
        if ((u8)*q++ != INSTR_POP
            || bc_find_label(ctx, index_off_bc) >= 0
            || bc_find_label(ctx, assign_off) >= 0
            || bc_find_label(ctx, pop_off) >= 0
            || !bc_cfg_same_block(
                    ctx, load_off, index_off_bc, assign_off
               )
            || !bc_cfg_same_block(ctx, assign_off, pop_off, pop_off)) {
                return false;
        }
#ifdef TY_PROFILER
        bc_emit_profiler_tick_at(ctx, code + index_off_bc);
        bc_emit_profiler_tick_at(ctx, code + assign_off);
        bc_emit_profiler_tick_at(ctx, code + pop_off);
#endif
        dasm_State **asm = &ctx->asm;
        int value_off = OP_OFF(ctx->sp - 1), array_off = array_local * VALUE_SIZE;
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S3, BC_LOC, array_off);
        jit_emit_decode_direct_array(asm, BC_S1, BC_S3, lbl_slow);
        if (index_local >= 0) {
                jit_emit_ldr64(asm, BC_S0, BC_LOC, index_local * VALUE_SIZE);
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_HIGH16_TAG);
                jit_emit_and(asm, BC_S3, BC_S0, BC_S2);
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_MIN_NUMBER);
                jit_emit_cmp_rr(asm, BC_S3, BC_S2);
                jit_emit_branch_ne(asm, lbl_slow);
                bc_decode_int32(ctx, BC_S0, BC_S0);
        } else {
                if (immediate < INT32_MIN || immediate > INT32_MAX) return false;
                jit_emit_load_imm(asm, BC_S0, immediate);
        }
        jit_emit_ldr64(asm, BC_S2, BC_S1, offsetof(Array, count));
        int lbl_nonneg = bc_next_label(ctx);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_ge(asm, lbl_nonneg);
        jit_emit_add(asm, BC_S0, BC_S0, BC_S2); jit_emit_label(asm, lbl_nonneg);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_lt(asm, lbl_slow);
        jit_emit_cmp_rr(asm, BC_S0, BC_S2); jit_emit_branch_ge(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S1, BC_S1, offsetof(Array, items));
        jit_emit_ldr64(asm, BC_S3, BC_OPS, value_off);
        jit_emit_str64_index8(asm, BC_S3, BC_S1, BC_S0);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_LOC, array_off);
        int idx_off = OP_OFF(ctx->sp + 1);
        if (index_local >= 0) bc_copy_value(ctx, BC_OPS, idx_off, BC_LOC, index_local * VALUE_SIZE);
        else {
                Value iv = value_integer(ctx->ty, immediate);
                if (nanbox_is_pointer(iv.bits)) gc_immortalize(ctx->ty, &iv);
                jit_emit_load_imm(asm, BC_S0, iv.bits.as_int64);
                jit_emit_str64(asm, BC_S0, BC_OPS, idx_off);
        }
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp + 2));
        jit_emit_load_imm(asm, BC_A2, 1);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_assign_subscript);
        bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        --ctx->sp;
        *ip = q;
        return true;
}

static bool
bc_try_local_array_get(JitCtx *ctx, char const *code, char const *end,
                       char const **ip, Symbol **locals,
                       int load_off, int array_local)
{
        if (getenv("TY_JIT_NO_LOCAL_ARRAY_GET") != NULL
            || array_local < 0 || array_local >= ctx->bound) return false;
        Class *array_class = expected_class_of(ctx->ty, locals[array_local]->type);
        if (array_class == NULL || array_class->i != CLASS_ARRAY) return false;
        char const *q = *ip;
        int index_off_bc = (int)(q - code), index_local = -1;
        imax immediate = 0;
        if (q < end && (u8)*q == INSTR_LOAD_LOCAL) {
                ++q;
                if (q + sizeof index_local > end) return false;
                __builtin_memcpy(&index_local, q, sizeof index_local); q += sizeof index_local;
#ifndef TY_NO_LOG
                q += strlen(q) + 1;
#endif
                if (index_local < 0 || index_local >= ctx->bound) return false;
                Class *ic = expected_class_of(ctx->ty, locals[index_local]->type);
                if (ic == NULL || ic->i != CLASS_INT) return false;
        } else if (q < end && (u8)*q == INSTR_INT8) {
                ++q; if (q >= end) return false; immediate = (i8)*q++;
        } else if (q < end && (u8)*q == INSTR_INTEGER) {
                ++q; if (q + sizeof immediate > end) return false;
                __builtin_memcpy(&immediate, q, sizeof immediate); q += sizeof immediate;
        } else return false;
        int subscript_off = (int)(q - code);
        if (q >= end || (u8)*q++ != INSTR_SUBSCRIPT
            || bc_find_label(ctx, index_off_bc) >= 0
            || bc_find_label(ctx, subscript_off) >= 0
            || !bc_cfg_same_block(ctx, load_off, index_off_bc, subscript_off)) return false;
#ifdef TY_PROFILER
        bc_emit_profiler_tick_at(ctx, code + index_off_bc);
        bc_emit_profiler_tick_at(ctx, code + subscript_off);
#endif
        dasm_State **asm = &ctx->asm;
        int array_off = array_local * VALUE_SIZE, result_off = OP_OFF(ctx->sp);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        /* Decode the direct Array tag and pointer. */
        jit_emit_ldr64(asm, BC_S3, BC_LOC, array_off);
        jit_emit_decode_direct_array(asm, BC_S1, BC_S3, lbl_slow);
        if (index_local >= 0) {
                jit_emit_ldr64(asm, BC_S0, BC_LOC, index_local * VALUE_SIZE);
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_HIGH16_TAG);
                jit_emit_and(asm, BC_S3, BC_S0, BC_S2);
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_MIN_NUMBER);
                jit_emit_cmp_rr(asm, BC_S3, BC_S2);
                jit_emit_branch_ne(asm, lbl_slow);
                bc_decode_int32(ctx, BC_S0, BC_S0);
        } else {
                if (immediate < INT32_MIN || immediate > INT32_MAX) return false;
                jit_emit_load_imm(asm, BC_S0, immediate);
        }
        jit_emit_ldr64(asm, BC_S2, BC_S1, offsetof(Array, count));
        int lbl_nonneg = bc_next_label(ctx);
        jit_emit_cmp_ri(asm, BC_S0, 0);
        jit_emit_branch_ge(asm, lbl_nonneg);
        jit_emit_add(asm, BC_S0, BC_S0, BC_S2);
        jit_emit_label(asm, lbl_nonneg);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_lt(asm, lbl_slow);
        jit_emit_cmp_rr(asm, BC_S0, BC_S2); jit_emit_branch_ge(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S1, BC_S1, offsetof(Array, items));
        jit_emit_ldr64_index8(asm, BC_S0, BC_S1, BC_S0);
        jit_emit_str64(asm, BC_S0, BC_OPS, result_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        bc_copy_value(ctx, BC_OPS, result_off, BC_LOC, array_off);
        int idx_off = OP_OFF(ctx->sp + 1);
        if (index_local >= 0) bc_copy_value(ctx, BC_OPS, idx_off, BC_LOC, index_local * VALUE_SIZE);
        else {
                Value iv = value_integer(ctx->ty, immediate);
                if (nanbox_is_pointer(iv.bits)) gc_immortalize(ctx->ty, &iv);
                jit_emit_load_imm(asm, BC_S0, iv.bits.as_int64);
                jit_emit_str64(asm, BC_S0, BC_OPS, idx_off);
        }
        jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_subscript); bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        ctx->op_types[ctx->sp] = NULL; ++ctx->sp;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
        *ip = q; return true;
}

static bool
bc_try_range_guard(JitCtx *ctx, char const *code, char const *end,
                   char const **ip, Symbol **locals, int dup_off)
{
        if (getenv("TY_JIT_NO_RANGE_GUARD") != NULL
            || ctx->sp < 2 || *ip + 1 + sizeof(i32) > end) {
                return false;
        }
        char const *q = *ip;
        int jump_off = (int)(q - code);
        u8 op = (u8)*q++;
        if (op != INSTR_JGE && op != INSTR_JGT && op != INSTR_JLT) {
                return false;
        }
        i32 rel;
        __builtin_memcpy(&rel, q, sizeof rel);
        q += sizeof rel;
        int target = (int)(q - code) + rel;
        int loop_target_off = (int)(q - code);
        if (q + 1 + sizeof(int) > end || (u8)*q++ != INSTR_TARGET_LOCAL) {
                return false;
        }
        int loop_local;
        __builtin_memcpy(&loop_local, q, sizeof loop_local);
        q += sizeof loop_local;
#ifndef TY_NO_LOG
        q += strlen(q) + 1;
#endif
        int assign_off = (int)(q - code);
        if (q >= end || (u8)*q++ != INSTR_ASSIGN
            || loop_local < 0 || loop_local >= ctx->bound) {
                return false;
        }
        int lbl_target = bc_find_label(ctx, target);
        Class *bound_class = expected_class_of(
                ctx->ty, ctx->op_types[ctx->sp - 2]
        );
        Class *cursor_class = expected_class_of(
                ctx->ty, ctx->op_types[ctx->sp - 1]
        );
        if (rel < 0 || lbl_target < 0
            || bound_class == NULL || bound_class->i != CLASS_INT
            || cursor_class == NULL || cursor_class->i != CLASS_INT
            || bc_find_label(ctx, jump_off) >= 0
            || bc_find_label(ctx, loop_target_off) >= 0
            || bc_find_label(ctx, assign_off) >= 0
            || !bc_cfg_same_block(ctx, dup_off, jump_off, jump_off)
            || !bc_cfg_same_block(
                    ctx, loop_target_off, assign_off, assign_off
               )) {
                return false;
        }
#ifdef TY_PROFILER
        bc_emit_profiler_tick_at(ctx, code + jump_off);
        bc_emit_profiler_tick_at(ctx, code + loop_target_off);
        bc_emit_profiler_tick_at(ctx, code + assign_off);
#endif
        dasm_State **asm = &ctx->asm;
        int bound_off = OP_OFF(ctx->sp - 2);
        int cursor_off = OP_OFF(ctx->sp - 1);
        int lbl_slow = bc_next_label(ctx);
        int lbl_assign = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, bound_off);
        jit_emit_ldr64(asm, BC_S0, BC_OPS, cursor_off);
        jit_emit_branch_not_int32(asm, BC_S1, lbl_slow);
        jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
        EMIT_STAT(jit_rt_stat_jcmp_int);
        bc_decode_int32(ctx, BC_S0, BC_S0);
        bc_decode_int32(ctx, BC_S1, BC_S1);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
        if (op == INSTR_JGE) {
                jit_emit_branch_ge(asm, lbl_target);
        } else if (op == INSTR_JGT) {
                jit_emit_branch_gt(asm, lbl_target);
        } else {
                jit_emit_branch_lt(asm, lbl_target);
        }
        jit_emit_jump(asm, lbl_assign);

        jit_emit_label(asm, lbl_slow);
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, cursor_off);
        jit_emit_add_imm(asm, BC_A2, BC_OPS, bound_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_compare);
        bc_emit_runtime_call(ctx, BC_CALL);
        /* Reload clobbers BC_RET on x64, but preserves comparison flags. */
        jit_emit_cmp_ri32(asm, BC_RET, 0);
        jit_emit_reload_stack(asm, ctx->bound);
        if (op == INSTR_JGE) {
                jit_emit_branch_ge(asm, lbl_target);
        } else if (op == INSTR_JGT) {
                jit_emit_branch_gt(asm, lbl_target);
        } else {
                jit_emit_branch_lt(asm, lbl_target);
        }
        jit_emit_label(asm, lbl_assign);
        bc_copy_value(
                ctx, BC_LOC, loop_local * VALUE_SIZE,
                BC_OPS, cursor_off
        );
        bc_raw_kill(ctx, loop_local);
        bc_set_label_sp(ctx, target, ctx->sp);
        *ip = q;
        return true;
}

static bool
bc_try_local_condition(JitCtx *ctx, char const *code, char const *end,
                       char const **ip, Symbol **locals, int load_off, int local)
{
        if (getenv("TY_JIT_NO_LOCAL_CONDITION") != NULL) {
                return false;
        }
        char const *q = *ip;
        if (q + 1 + sizeof(i32) > end || local < 0 || local >= ctx->bound) {
                return false;
        }
        int branch_off = (int)(q - code);
        u8 op = (u8)*q++;
        if (op != INSTR_JUMP_IF && op != INSTR_JUMP_IF_NOT) {
                return false;
        }
        i32 rel;
        __builtin_memcpy(&rel, q, sizeof rel);
        q += sizeof rel;
        int target = (int)(q - code) + rel;
        Class *class = expected_class_of(ctx->ty, locals[local]->type);
        int lbl_target = bc_find_label(ctx, target);
        if (rel < 0 || lbl_target < 0 || class == NULL
            || (class->i != CLASS_INT && class->i != CLASS_BOOL)
            || bc_find_label(ctx, branch_off) >= 0
            || !bc_cfg_same_block(ctx, load_off, branch_off, branch_off)) {
                return false;
        }
#ifdef TY_PROFILER
        bc_emit_profiler_tick_at(ctx, code + branch_off);
#endif
        dasm_State **asm = &ctx->asm;
        int lbl_slow = bc_next_label(ctx), lbl_test = bc_next_label(ctx);
        int local_off = local * VALUE_SIZE;
        jit_emit_ldr64(asm, BC_S0, BC_LOC, local_off);
        if (class->i == CLASS_INT) {
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_HIGH16_TAG);
                jit_emit_and(asm, BC_S3, BC_S0, BC_S2);
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_MIN_NUMBER);
                jit_emit_cmp_rr(asm, BC_S3, BC_S2);
                jit_emit_branch_ne(asm, lbl_slow);
                bc_decode_int32(ctx, BC_S0, BC_S0);
        } else {
                jit_emit_load_imm(asm, BC_S2, (i64)~UINT64_C(1));
                jit_emit_and(asm, BC_S3, BC_S0, BC_S2);
                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_VALUE_FALSE);
                jit_emit_cmp_rr(asm, BC_S3, BC_S2); jit_emit_branch_ne(asm, lbl_slow);
                jit_emit_load_imm(asm, BC_S2, 1); jit_emit_and(asm, BC_S0, BC_S0, BC_S2);
        }
        jit_emit_jump(asm, lbl_test);
        jit_emit_label(asm, lbl_slow);
        jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_LOC, local_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_truthy); bc_emit_runtime_call(ctx, BC_CALL);
        jit_emit_mov(asm, BC_S0, BC_RET); jit_emit_label(asm, lbl_test);
        if (op == INSTR_JUMP_IF) jit_emit_cbnz(asm, BC_S0, lbl_target);
        else jit_emit_cbz(asm, BC_S0, lbl_target);
        bc_set_label_sp(ctx, target, ctx->sp);
        *ip = q;
        return true;
}

static bool
bc_try_local_subscript(JitCtx *ctx, char const *code, char const *end,
                       char const **ip, Symbol **locals, int load_off, int local)
{
        if (getenv("TY_JIT_NO_LOCAL_SUBSCRIPT") != NULL
            || *ip >= end || (u8)**ip != INSTR_SUBSCRIPT
            || ctx->sp < 1 || local < 0 || local >= ctx->bound) return false;
        int subscript_off = (int)(*ip - code);
        Class *index_class = expected_class_of(ctx->ty, locals[local]->type);
        Class *container_class = expected_class_of(ctx->ty, ctx->op_types[ctx->sp - 1]);
        if (index_class == NULL || index_class->i != CLASS_INT
            || container_class == NULL || container_class->i != CLASS_ARRAY
            || bc_find_label(ctx, subscript_off) >= 0
            || !bc_cfg_same_block(ctx, load_off, subscript_off, subscript_off)) return false;
#ifdef TY_PROFILER
        bc_emit_profiler_tick_at(ctx, code + subscript_off);
#endif
        dasm_State **asm = &ctx->asm;
        int result_off = OP_OFF(ctx->sp - 1), index_off = local * VALUE_SIZE;
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, result_off);
        jit_emit_decode_direct_array(asm, BC_S1, BC_S1, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_LOC, index_off);
        jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
        bc_decode_int32(ctx, BC_S0, BC_S0);
        jit_emit_ldr64(asm, BC_S2, BC_S1, offsetof(Array, count));
        jit_emit_cmp_ri(asm, BC_S0, 0);
        jit_emit_branch_lt(asm, lbl_slow);
        jit_emit_cmp_rr(asm, BC_S0, BC_S2);
        jit_emit_branch_ge(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S1, BC_S1, offsetof(Array, items));
        jit_emit_ldr64_index8(asm, BC_S0, BC_S1, BC_S0);
        jit_emit_str64(asm, BC_S0, BC_OPS, result_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_LOC, index_off);
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_subscript);
        bc_emit_runtime_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        ++*ip;
        return true;
}

static bool
bc_try_local_int_jcmp(JitCtx *ctx, char const *code, char const *end,
                      char const **ip, Symbol **locals, int first_off, int left)
{
        if (getenv("TY_JIT_NO_LOCAL_JCMP") != NULL) {
                return false;
        }
        char const *q = *ip;
        int right = -1;
        imax immediate = 0;
        int operand_off = (int)(q - code);
        if (q >= end) {
                return false;
        }
        if ((u8)*q == INSTR_LOAD_LOCAL) {
                ++q;
                if (q + sizeof right > end) {
                        return false;
                }
                __builtin_memcpy(&right, q, sizeof right);
                q += sizeof right;
#ifndef TY_NO_LOG
                q += strlen(q) + 1;
#endif
        } else if ((u8)*q == INSTR_INT8) {
                ++q;
                if (q >= end) {
                        return false;
                }
                immediate = (i8)*q++;
        } else if ((u8)*q == INSTR_INTEGER) {
                ++q;
                if (q + sizeof immediate > end) {
                        return false;
                }
                __builtin_memcpy(&immediate, q, sizeof immediate);
                q += sizeof immediate;
        } else {
                return false;
        }
        int cmp_off = (int)(q - code);
        if (q + 1 + sizeof(i32) > end) {
                return false;
        }
        u8 op = (u8)*q++;
        if (op != INSTR_JLT && op != INSTR_JGT
            && op != INSTR_JLE && op != INSTR_JGE) {
                return false;
        }
        i32 rel;
        __builtin_memcpy(&rel, q, sizeof rel);
        q += sizeof rel;
        if (rel < 0) {
                return false;
        }
        int target = (int)(q - code) + rel;
        int lbl_target = bc_find_label(ctx, target);
        Class *left_class = left >= 0 && left < ctx->bound
                ? expected_class_of(ctx->ty, locals[left]->type) : NULL;
        Class *right_class = right >= 0 && right < ctx->bound
                ? expected_class_of(ctx->ty, locals[right]->type) : NULL;
        if (lbl_target < 0
            || left_class == NULL || left_class->i != CLASS_INT
            || (right >= 0
                && (right_class == NULL || right_class->i != CLASS_INT))
            || bc_find_label(ctx, operand_off) >= 0
            || bc_find_label(ctx, cmp_off) >= 0
            || !bc_cfg_same_block(ctx, first_off, operand_off, cmp_off)) {
                return false;
        }
#ifdef TY_PROFILER
        bc_emit_profiler_tick_at(ctx, code + operand_off);
        bc_emit_profiler_tick_at(ctx, code + cmp_off);
#endif
        bc_emit_int_local_jcmp(ctx, left, right, immediate, op, lbl_target);
        bc_set_label_sp(ctx, target, ctx->sp);
        *ip = q;
        return true;
}

static void
bc_emit_numeric_mut(JitCtx *ctx, int source_reg, int source_off,
                    bool materialize_source, bool keep_result,
                    int target, u8 op, int class_id)
{
        dasm_State **asm = &ctx->asm;
        int target_off = target * VALUE_SIZE, scratch_off = OP_OFF(ctx->sp);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        if (class_id != CLASS_INT) {
                /* This fusion is currently admitted only for integer locals. */
                jit_emit_jump(asm, lbl_slow);
        } else {
                jit_emit_ldr64(asm, BC_S0, BC_LOC, target_off);
                jit_emit_ldr64(asm, BC_S1, source_reg, source_off);
                jit_emit_load_imm(asm, BC_RET, (i64)NANBOX_HIGH16_TAG);
                jit_emit_and(asm, BC_S3, BC_S0, BC_RET);
                jit_emit_load_imm(asm, BC_CALL, (i64)NANBOX_MIN_NUMBER);
                jit_emit_cmp_rr(asm, BC_S3, BC_CALL); jit_emit_branch_ne(asm, lbl_slow);
                jit_emit_and(asm, BC_S3, BC_S1, BC_RET);
                jit_emit_cmp_rr(asm, BC_S3, BC_CALL); jit_emit_branch_ne(asm, lbl_slow);
                bc_decode_int32(ctx, BC_S0, BC_S0); bc_decode_int32(ctx, BC_S1, BC_S1);
                if (op == INSTR_MUT_ADD) jit_emit_add32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
                else if (op == INSTR_MUT_SUB) jit_emit_sub32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
                else jit_emit_mul32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
                bc_encode_int32(ctx, BC_S0, BC_S0);
                jit_emit_str64(asm, BC_S0, BC_LOC, target_off);
                if (keep_result) jit_emit_str64(asm, BC_S0, source_reg, source_off);
                jit_emit_jump(asm, lbl_done);
        }
        jit_emit_label(asm, lbl_slow);
        if (materialize_source) {
                bc_copy_value(ctx, BC_OPS, scratch_off, source_reg, source_off);
                source_reg = BC_OPS; source_off = scratch_off;
        }
        jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_LOC, target_off);
        jit_emit_add_imm(asm, BC_A2, source_reg, source_off); jit_emit_mov(asm, BC_A3, BC_A2);
        jit_emit_load_imm(asm, BC_CALL, (iptr)bc_mut_runtime(op)); bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
}

static void
bc_emit_local_int_imm_mut_pop(JitCtx *ctx, int target, u8 op, imax value)
{
        dasm_State **asm = &ctx->asm;
        int target_off = target * VALUE_SIZE, scratch_off = OP_OFF(ctx->sp);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S0, BC_LOC, target_off);
        jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
        bc_decode_int32(ctx, BC_S0, BC_S0); jit_emit_load_imm(asm, BC_S1, value);
        if (op == INSTR_MUT_ADD) jit_emit_add32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
        else if (op == INSTR_MUT_SUB) jit_emit_sub32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
        else jit_emit_mul32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
        bc_encode_int32(ctx, BC_S0, BC_S0); jit_emit_str64(asm, BC_S0, BC_LOC, target_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        Value iv = value_integer(ctx->ty, value);
        if (nanbox_is_pointer(iv.bits)) gc_immortalize(ctx->ty, &iv);
        jit_emit_load_imm(asm, BC_S0, iv.bits.as_int64); jit_emit_str64(asm, BC_S0, BC_OPS, scratch_off);
        jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_LOC, target_off);
        jit_emit_add_imm(asm, BC_A2, BC_OPS, scratch_off); jit_emit_mov(asm, BC_A3, BC_A2);
        jit_emit_load_imm(asm, BC_CALL, (iptr)bc_mut_runtime(op)); bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
}

#ifdef TY_PROFILER
static void
bc_emit_profiler_tick_at(JitCtx *ctx, char const *ip)
{
        dasm_State **asm = &ctx->asm;
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_load_imm(asm, BC_A1, (iptr)ip);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_profiler_tick);
        bc_emit_runtime_call(ctx, BC_CALL);
}
#endif

static bool
bc_try_local_int_imm_mut_pop(JitCtx *ctx, char const *code, char const *end,
                             char const **ip, Symbol **locals, imax value)
{
        char const *q = *ip;
        if (q + 1 + sizeof(int) + 2 > end
            || (u8)*q != INSTR_TARGET_LOCAL) {
                return false;
        }
        int target_offset = (int)(q - code);
        int target;
        ++q;
        __builtin_memcpy(&target, q, sizeof target);
        q += sizeof target;
        int mut_offset = (int)(q - code);
        u8 op = (u8)*q++;
        int pop_offset = (int)(q - code);
        Class *target_class = target >= 0 && target < ctx->bound
                ? expected_class_of(ctx->ty, locals[target]->type)
                : NULL;
        if ((op != INSTR_MUT_ADD
             && op != INSTR_MUT_SUB
             && op != INSTR_MUT_MUL)
            || (u8)*q != INSTR_POP
            || target_class == NULL
            || target_class->i != CLASS_INT
            || bc_find_label(ctx, target_offset) >= 0
            || bc_find_label(ctx, mut_offset) >= 0
            || bc_find_label(ctx, pop_offset) >= 0
            || !bc_cfg_same_block(
                    ctx, target_offset, mut_offset, pop_offset
               )) {
                return false;
        }
#ifdef TY_PROFILER
        bc_emit_profiler_tick_at(ctx, code + target_offset);
        bc_emit_profiler_tick_at(ctx, code + mut_offset);
        bc_emit_profiler_tick_at(ctx, code + pop_offset);
#endif
        bc_emit_local_int_imm_mut_pop(ctx, target, op, value);
        *ip = q + 1;
        return true;
}

static bool
bc_emit_builtin_count(JitCtx *ctx)
{
        /* Legacy field-offset implementation below assumes inline Value
         * payloads.  The generic helper is canonical for nanboxed Values. */
        if (VALUE_SIZE == 8) return false;
        if (getenv("TY_JIT_NO_BUILTIN_COUNT") != NULL) {
                return false;
        }
        Class *class = expected_class_of(
                ctx->ty, ctx->op_types[ctx->sp - 1]
        );
        if (class == NULL
            || (class->i != CLASS_ARRAY
                && class->i != CLASS_BLOB
                && class->i != CLASS_DICT)) {
                return false;
        }
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp - 1);
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);
        int type = class->i == CLASS_ARRAY ? VALUE_ARRAY
                 : class->i == CLASS_TUPLE ? VALUE_TUPLE
                 : class->i == CLASS_BLOB ? VALUE_BLOB : VALUE_DICT;
        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, type);
        jit_emit_branch_ne(asm, lbl_slow);
        if (class->i == CLASS_TUPLE) {
                jit_emit_ldr32(asm, BC_S2, BC_OPS, off + VAL_OFF_COUNT);
        } else {
                jit_emit_ldr64(asm, BC_S1, BC_OPS, off + VAL_OFF_Z);
                int count_off = class->i == CLASS_DICT
                        ? OFF_DICT_COUNT : OFF_VEC_LEN;
                jit_emit_ldr64(asm, BC_S2, BC_S1, count_off);
        }
        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
        jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
        jit_emit_str64(asm, BC_S2, BC_OPS, off + VAL_OFF_Z);
        jit_emit_jump(asm, lbl_done);

        jit_emit_label(asm, lbl_slow);
        bc_emit_unop_helper(ctx, (void *)jit_rt_count);
        jit_emit_label(asm, lbl_done);
        return true;
}

static void
bc_emit_arith(JitCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;
        int a_off = OP_OFF(ctx->sp - 2);
        int b_off = OP_OFF(ctx->sp - 1);
        int lbl_float = bc_next_label(ctx);
        int lbl_b_double = bc_next_label(ctx);
        int lbl_float_ready = bc_next_label(ctx);
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);

        bool int_fast = helper == (void *)jit_rt_add
                     || helper == (void *)jit_rt_sub
                     || helper == (void *)jit_rt_mul
                     || helper == (void *)jit_rt_div
                     || helper == (void *)jit_rt_mod;
        bool float_fast = helper == (void *)jit_rt_add
                       || helper == (void *)jit_rt_sub
                       || helper == (void *)jit_rt_mul
                       || helper == (void *)jit_rt_div;
        if (!int_fast && !float_fast) {
                bc_emit_binop_helper(ctx, helper);
                return;
        }

        jit_emit_ldr64(asm, BC_S0, BC_OPS, a_off);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, b_off);

        if (int_fast) {
                jit_emit_branch_not_int32(asm, BC_S0, lbl_float);
                jit_emit_branch_not_int32(asm, BC_S1, lbl_slow);

                bc_decode_int32(ctx, BC_S0, BC_S0);
                bc_decode_int32(ctx, BC_S1, BC_S1);
                if (helper == (void *)jit_rt_add) {
                        jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
                } else if (helper == (void *)jit_rt_sub) {
                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                } else if (helper == (void *)jit_rt_mul) {
                        jit_emit_mul(asm, BC_S0, BC_S0, BC_S1);
                } else {
                        jit_emit_cmp_ri(asm, BC_S1, 0);
                        jit_emit_branch_eq(asm, lbl_slow);
                        int lbl_safe_div = bc_next_label(ctx);
                        jit_emit_load_imm(asm, BC_S2, INT32_MIN);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S2);
                        jit_emit_branch_ne(asm, lbl_safe_div);
                        jit_emit_cmp_ri(asm, BC_S1, -1);
                        jit_emit_branch_eq(asm, lbl_slow);
                        jit_emit_label(asm, lbl_safe_div);
                        if (helper == (void *)jit_rt_div)
                                jit_emit_sdiv(asm, BC_S0, BC_S0, BC_S1);
                        else
                                jit_emit_mod(asm, BC_S0, BC_S0, BC_S1);
                }
                if (helper == (void *)jit_rt_add || helper == (void *)jit_rt_sub
                    || helper == (void *)jit_rt_mul) {
                        jit_emit_load_imm(asm, BC_S2, 32);
                        jit_emit_shl(asm, BC_S1, BC_S0, BC_S2);
                        jit_emit_shr(asm, BC_S1, BC_S1, BC_S2);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
                        jit_emit_branch_ne(asm, lbl_slow);
                }
                bc_encode_int32(ctx, BC_S0, BC_S0);
                jit_emit_str64(asm, BC_S0, BC_OPS, a_off);
                jit_emit_jump(asm, lbl_done);
        }

        jit_emit_label(asm, lbl_float);
        if (!float_fast) {
                jit_emit_jump(asm, lbl_slow);
        }
        /* Mixed real/int is common in numeric kernels (notably spectralNorm).
         * Convert only the right-hand immediate int; boxed integers retain the
         * semantic helper path. */
        jit_emit_branch_not_double(asm, BC_S0, lbl_slow);
        jit_emit_branch_not_int32(asm, BC_S1, lbl_b_double);
        bc_decode_int32(ctx, BC_S1, BC_S1);
        jit_emit_int_to_double_bits(asm, BC_S1, BC_S1);
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_add(asm, BC_S1, BC_S1, BC_S2);
        jit_emit_jump(asm, lbl_float_ready);
        jit_emit_label(asm, lbl_b_double);
        jit_emit_branch_not_double(asm, BC_S1, lbl_slow);
        jit_emit_label(asm, lbl_float_ready);
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_sub(asm, BC_S0, BC_S0, BC_S2);
        jit_emit_sub(asm, BC_S1, BC_S1, BC_S2);
        int float_op = helper == (void *)jit_rt_add ? 0
                     : helper == (void *)jit_rt_sub ? 1
                     : helper == (void *)jit_rt_mul ? 2 : 3;
        jit_emit_farith_bits(asm, BC_S0, BC_S0, BC_S1, float_op);
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_add(asm, BC_S0, BC_S0, BC_S2);
        jit_emit_str64(asm, BC_S0, BC_OPS, a_off);
        jit_emit_jump(asm, lbl_done);

        jit_emit_label(asm, lbl_slow);
        bc_emit_binop_helper(ctx, helper);
        jit_emit_label(asm, lbl_done);
}

static void
bc_write_bool(JitCtx *ctx, int off, int val_reg)
{
        dasm_State **asm = &ctx->asm;
        jit_emit_load_imm(asm, BC_S1, (i64)NANBOX_VALUE_FALSE);
        jit_emit_or(asm, val_reg, val_reg, BC_S1);
        jit_emit_str64(asm, val_reg, BC_OPS, off);
}

static void
bc_emit_cmp(JitCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;
        int a_off = OP_OFF(ctx->sp - 2);
        int b_off = OP_OFF(ctx->sp - 1);
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);

        /* Immediate integers have a fixed high-16 tag and a signed 32-bit
         * payload.  Decode those words directly; boxed/full-width integers and
         * every other kind take the semantic helper path. */
        jit_emit_ldr64(asm, BC_S0, BC_OPS, a_off);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, b_off);
        jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
        jit_emit_branch_not_int32(asm, BC_S1, lbl_slow);

        bc_decode_int32(ctx, BC_S0, BC_S0);
        bc_decode_int32(ctx, BC_S1, BC_S1);

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
        } else {
                jit_emit_jump(asm, lbl_slow);
        }
        jit_emit_load_imm(asm, BC_S1, (i64)NANBOX_VALUE_FALSE);
        jit_emit_or(asm, BC_S0, BC_S0, BC_S1);
        jit_emit_str64(asm, BC_S0, BC_OPS, a_off);
        jit_emit_jump(asm, lbl_done);

        jit_emit_label(asm, lbl_slow);
        bc_emit_binop_helper(ctx, helper);
        jit_emit_label(asm, lbl_done);
}

static void
bc_emit_truthy(JitCtx *ctx)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp - 1);
        int lbl_false = bc_next_label(ctx), lbl_true = bc_next_label(ctx);
        int lbl_int = bc_next_label(ctx), lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S0, BC_OPS, off);
        jit_emit_cmp_ri(asm, BC_S0, NANBOX_VALUE_NULL);
        jit_emit_branch_eq(asm, lbl_false);
        jit_emit_cmp_ri(asm, BC_S0, NANBOX_VALUE_FALSE);
        jit_emit_branch_eq(asm, lbl_false);
        jit_emit_cmp_ri(asm, BC_S0, NANBOX_VALUE_TRUE);
        jit_emit_branch_eq(asm, lbl_true);
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_HIGH16_TAG);
        jit_emit_and(asm, BC_S1, BC_S0, BC_S2);
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_MIN_NUMBER);
        jit_emit_cmp_rr(asm, BC_S1, BC_S2);
        jit_emit_branch_eq(asm, lbl_int);
        jit_emit_jump(asm, lbl_slow);
        jit_emit_label(asm, lbl_int);
        bc_decode_int32(ctx, BC_S0, BC_S0);
        jit_emit_load_imm(asm, BC_S1, 0);
        jit_emit_cmp_ne(asm, BC_S0, BC_S0, BC_S1);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_false);
        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_true);
        jit_emit_load_imm(asm, BC_S0, 1);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_truthy);
        bc_emit_runtime_call(ctx, BC_CALL);
        jit_emit_mov(asm, BC_S0, BC_RET);
        jit_emit_label(asm, lbl_done);
}

static bool
bc_emit_member_read_fast(JitCtx *ctx, int member_id, char const *bc_ip)
{
        Type *type = ctx->op_types[ctx->sp - 1];
        Class *cls = expected_class_of(ctx->ty, type);
        if (cls == NULL || member_id >= (int)vN(cls->offsets_r)) return false;
        u16 off = v__(cls->offsets_r, member_id);
        if (off == OFF_NOT_FOUND || (off >> OFF_SHIFT) != OFF_FIELD) return false;
        int slot_off = OBJ_OFF_SLOTS + (off & OFF_MASK) * VALUE_SIZE;
        dasm_State **asm = &ctx->asm;
        int value_off = OP_OFF(ctx->sp - 1), lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S3, BC_OPS, value_off);
        jit_emit_decode_direct_object(asm, BC_S2, BC_S3, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_CLASS);
        jit_emit_load_imm(asm, BC_S1, (iptr)cls);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1); jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_DYN);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_ne(asm, lbl_slow);
        bc_copy_value(ctx, BC_OPS, value_off, BC_S2, slot_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        (void)bc_ip;
        jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_OPS, value_off);
        jit_emit_mov(asm, BC_A2, BC_A1); jit_emit_load_imm(asm, BC_A3, member_id);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member); bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        return true;
}

static bool
bc_emit_primitive_member(JitCtx *ctx, int member_id, char const *name)
{
        if (strcmp(name, "float") != 0 && strcmp(name, "abs") != 0) return false;
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp - 1);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S0, BC_OPS, off);
        if (strcmp(name, "float") == 0) {
                jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
                bc_decode_int32(ctx, BC_S0, BC_S0);
                jit_emit_int_to_double_bits(asm, BC_S0, BC_S0);
                jit_emit_load_imm(asm, BC_S1, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
                jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
        } else {
                jit_emit_branch_not_double(asm, BC_S0, lbl_slow);
                jit_emit_load_imm(asm, BC_S1, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
                jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                jit_emit_load_imm(asm, BC_S1, INT64_MAX);
                jit_emit_and(asm, BC_S0, BC_S0, BC_S1);
                jit_emit_load_imm(asm, BC_S1, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
                jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
        }
        jit_emit_str64(asm, BC_S0, BC_OPS, off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
        jit_emit_mov(asm, BC_A2, BC_A1);
        jit_emit_load_imm(asm, BC_A3, member_id);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
        bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        return true;
}

static void
bc_emit_member_read_dynamic(JitCtx *ctx, int member_id, char const *bc_ip)
{
        dasm_State **asm = &ctx->asm;
        int value_off = OP_OFF(ctx->sp - 1);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        int count_off = offsetof(Class, offsets_r) + offsetof(u16Vector, count);
        int items_off = offsetof(Class, offsets_r) + offsetof(u16Vector, items);
        jit_emit_ldr64(asm, BC_S3, BC_OPS, value_off);
        jit_emit_decode_direct_object(asm, BC_S2, BC_S3, lbl_slow);
        jit_emit_ldr64(asm, BC_S3, BC_S2, OBJ_OFF_CLASS);
        jit_emit_ldr64(asm, BC_S0, BC_S3, count_off);
        jit_emit_cmp_ri(asm, BC_S0, member_id);
        jit_emit_branch_le(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S3, BC_S3, items_off);
        jit_emit_load_imm(asm, BC_S1, member_id * (int)sizeof(u16));
        jit_emit_ldr16_index(asm, BC_S0, BC_S3, BC_S1);
        jit_emit_load_imm(asm, BC_S1, OFF_SHIFT);
        jit_emit_shr(asm, BC_S3, BC_S0, BC_S1);
        jit_emit_cmp_ri(asm, BC_S3, OFF_FIELD);
        jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_load_imm(asm, BC_S1, OFF_MASK);
        jit_emit_and(asm, BC_S0, BC_S0, BC_S1);
        jit_emit_add_imm(asm, BC_S2, BC_S2, OBJ_OFF_SLOTS);
        jit_emit_ldr64_index8(asm, BC_S0, BC_S2, BC_S0);
        jit_emit_str64(asm, BC_S0, BC_OPS, value_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        (void)bc_ip;
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, value_off);
        jit_emit_mov(asm, BC_A2, BC_A1);
        jit_emit_load_imm(asm, BC_A3, member_id);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
        bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
}

static void
bc_emit_member_write_dynamic(JitCtx *ctx, int member_id, char const *bc_ip)
{
        dasm_State **asm = &ctx->asm;
        int obj_off = OP_OFF(ctx->sp - 1), val_off = OP_OFF(ctx->sp - 2);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        int count_off = offsetof(Class, offsets_w) + offsetof(u16Vector, count);
        int items_off = offsetof(Class, offsets_w) + offsetof(u16Vector, items);
        jit_emit_ldr64(asm, BC_S3, BC_OPS, obj_off);
        jit_emit_decode_direct_object(asm, BC_S2, BC_S3, lbl_slow);
        jit_emit_ldr64(asm, BC_S3, BC_S2, OBJ_OFF_CLASS);
        jit_emit_ldr64(asm, BC_S0, BC_S3, count_off);
        jit_emit_cmp_ri(asm, BC_S0, member_id);
        jit_emit_branch_le(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S3, BC_S3, items_off);
        jit_emit_load_imm(asm, BC_S1, member_id * (int)sizeof(u16));
        jit_emit_ldr16_index(asm, BC_S0, BC_S3, BC_S1);
        jit_emit_load_imm(asm, BC_S1, OFF_SHIFT);
        jit_emit_shr(asm, BC_S3, BC_S0, BC_S1);
        jit_emit_cmp_ri(asm, BC_S3, OFF_FIELD);
        jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_load_imm(asm, BC_S1, OFF_MASK);
        jit_emit_and(asm, BC_S0, BC_S0, BC_S1);
        jit_emit_add_imm(asm, BC_S2, BC_S2, OBJ_OFF_SLOTS);
        jit_emit_ldr64(asm, BC_S3, BC_OPS, val_off);
        jit_emit_str64_index8(asm, BC_S3, BC_S2, BC_S0);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        (void)bc_ip;
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);
        jit_emit_load_imm(asm, BC_A2, member_id);
        jit_emit_add_imm(asm, BC_A3, BC_OPS, val_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member_set);
        bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        ctx->sp--;
}

static bool
bc_emit_member_mut_fast(JitCtx *ctx, int member_id, u8 op, char const *bc_ip)
{
        if (op != INSTR_MUT_ADD && op != INSTR_MUT_SUB && op != INSTR_MUT_MUL
            && op != INSTR_MUT_DIV) return false;
        Class *cls = expected_class_of(ctx->ty, ctx->op_types[ctx->sp - 1]);
        if (cls == NULL || member_id >= (int)vN(cls->offsets_w)) return false;
        u16 off = v__(cls->offsets_w, member_id);
        if (off == OFF_NOT_FOUND || (off >> OFF_SHIFT) != OFF_FIELD) return false;
        int slot_off = OBJ_OFF_SLOTS + (off & OFF_MASK) * VALUE_SIZE;
        dasm_State **asm = &ctx->asm;
        int obj_off = OP_OFF(ctx->sp - 1), val_off = OP_OFF(ctx->sp - 2);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S3, BC_OPS, obj_off);
        jit_emit_decode_direct_object(asm, BC_S2, BC_S3, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_CLASS);
        jit_emit_load_imm(asm, BC_S1, (iptr)cls);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1); jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_DYN);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_ne(asm, lbl_slow);
        /* Native encoded-double mutation. */
        jit_emit_ldr64(asm, BC_S0, BC_S2, slot_off);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, val_off);
        jit_emit_branch_not_double(asm, BC_S0, lbl_slow);
        jit_emit_branch_not_double(asm, BC_S1, lbl_slow);
        jit_emit_load_imm(asm, BC_S3, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_sub(asm, BC_S0, BC_S0, BC_S3); jit_emit_sub(asm, BC_S1, BC_S1, BC_S3);
        int arith = op == INSTR_MUT_ADD ? 0 : op == INSTR_MUT_SUB ? 1
                  : op == INSTR_MUT_MUL ? 2 : 3;
        jit_emit_farith_bits(asm, BC_S0, BC_S0, BC_S1, arith);
        jit_emit_load_imm(asm, BC_S3, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_add(asm, BC_S0, BC_S0, BC_S3);
        jit_emit_str64(asm, BC_S0, BC_S2, slot_off); jit_emit_str64(asm, BC_S0, BC_OPS, val_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        (void)bc_ip;
        void *runtime = op == INSTR_MUT_ADD ? (void *)jit_rt_member_mut_add
                : op == INSTR_MUT_SUB ? (void *)jit_rt_member_mut_sub
                : op == INSTR_MUT_MUL ? (void *)jit_rt_member_mut_mul
                                      : (void *)jit_rt_member_mut_div;
        jit_emit_mov(asm, BC_A0, BC_TY); jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);
        jit_emit_load_imm(asm, BC_A2, member_id); jit_emit_add_imm(asm, BC_A3, BC_OPS, val_off);
        jit_emit_add_imm(asm, BC_A4, BC_OPS, val_off); jit_emit_load_imm(asm, BC_CALL, (iptr)runtime);
        bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        return true;
}

static void
bc_emit_self_object(JitCtx *ctx, int out_reg, int lbl_slow)
{
        dasm_State **asm = &ctx->asm;
        int self_off = ctx->param_count * VALUE_SIZE;
        int lbl_box = bc_next_label(ctx);
        int lbl_decode = bc_next_label(ctx);
        jit_emit_ldr64(asm, BC_S3, BC_LOC, self_off);
        jit_emit_branch_not_pointer(asm, BC_S3, lbl_decode);
        jit_emit_label(asm, lbl_box);
        jit_emit_ldrb(asm, BC_S0, BC_S3, offsetof(ValueBox, payload.type));
        jit_emit_cmp_ri(asm, BC_S0, VALUE_REF);
        jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S3, BC_S3, offsetof(ValueBox, payload.ref));
        jit_emit_ldr64(asm, BC_S3, BC_S3, 0);
        jit_emit_label(asm, lbl_decode);
        jit_emit_decode_direct_object(asm, out_reg, BC_S3, lbl_slow);
}

static bool
bc_emit_self_member_read_fast(JitCtx *ctx, int member_id, char const *bc_ip)
{
        if (ctx->self_class == NULL || member_id >= (int)vN(ctx->self_class->offsets_r)) return false;
        u16 off = v__(ctx->self_class->offsets_r, member_id);
        if (off == OFF_NOT_FOUND || (off >> OFF_SHIFT) != OFF_FIELD) return false;
        int slot_off = OBJ_OFF_SLOTS + (off & OFF_MASK) * VALUE_SIZE;
        dasm_State **asm = &ctx->asm;
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        int out_off = OP_OFF(ctx->sp++);
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
        bc_emit_self_object(ctx, BC_S2, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_CLASS);
        jit_emit_load_imm(asm, BC_S1, (iptr)ctx->self_class);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1); jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_DYN);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_ne(asm, lbl_slow);
        bc_copy_value(ctx, BC_OPS, out_off, BC_S2, slot_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        (void)bc_ip;
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, out_off);
        jit_emit_load_imm(asm, BC_A2, 0);
        jit_emit_load_imm(asm, BC_A3, member_id);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
        bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        return true;
}

// Type-guided fast path: TARGET_SELF_MEMBER + ASSIGN with known class
static bool
bc_emit_self_member_write_fast(JitCtx *ctx, int member_id, char const *bc_ip)
{
        if (ctx->self_class == NULL || member_id >= (int)vN(ctx->self_class->offsets_w)) return false;
        u16 off = v__(ctx->self_class->offsets_w, member_id);
        if (off == OFF_NOT_FOUND || (off >> OFF_SHIFT) != OFF_FIELD) return false;
        int slot_off = OBJ_OFF_SLOTS + (off & OFF_MASK) * VALUE_SIZE;
        dasm_State **asm = &ctx->asm;
        int val_off = OP_OFF(ctx->sp - 1);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        bc_emit_self_object(ctx, BC_S2, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_CLASS);
        jit_emit_load_imm(asm, BC_S1, (iptr)ctx->self_class);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1); jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_DYN);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_ne(asm, lbl_slow);
        bc_copy_value(ctx, BC_S2, slot_off, BC_OPS, val_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        (void)bc_ip;
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_load_imm(asm, BC_A1, 0);
        jit_emit_load_imm(asm, BC_A2, member_id);
        jit_emit_add_imm(asm, BC_A3, BC_OPS, val_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member_set);
        bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        return true;
}

static bool
bc_emit_self_member_mut_fast(JitCtx *ctx, int member_id, u8 op, char const *bc_ip)
{
        if (ctx->self_class == NULL
            || (op != INSTR_MUT_ADD && op != INSTR_MUT_SUB
                && op != INSTR_MUT_MUL && op != INSTR_MUT_DIV)
            || member_id >= (int)vN(ctx->self_class->offsets_w)) return false;
        u16 off = v__(ctx->self_class->offsets_w, member_id);
        if (off == OFF_NOT_FOUND || (off >> OFF_SHIFT) != OFF_FIELD) return false;
        int slot_off = OBJ_OFF_SLOTS + (off & OFF_MASK) * VALUE_SIZE;
        dasm_State **asm = &ctx->asm;
        int val_off = OP_OFF(ctx->sp - 1);
        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
        bc_emit_self_object(ctx, BC_S2, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_CLASS);
        jit_emit_load_imm(asm, BC_S1, (iptr)ctx->self_class);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1); jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_DYN);
        jit_emit_cmp_ri(asm, BC_S0, 0); jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, slot_off);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, val_off);
        jit_emit_branch_not_double(asm, BC_S0, lbl_slow);
        jit_emit_branch_not_double(asm, BC_S1, lbl_slow);
        jit_emit_load_imm(asm, BC_S3, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_sub(asm, BC_S0, BC_S0, BC_S3);
        jit_emit_sub(asm, BC_S1, BC_S1, BC_S3);
        int arith = op == INSTR_MUT_ADD ? 0 : op == INSTR_MUT_SUB ? 1
                  : op == INSTR_MUT_MUL ? 2 : 3;
        jit_emit_farith_bits(asm, BC_S0, BC_S0, BC_S1, arith);
        jit_emit_load_imm(asm, BC_S3, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_add(asm, BC_S0, BC_S0, BC_S3);
        jit_emit_str64(asm, BC_S0, BC_S2, slot_off);
        jit_emit_str64(asm, BC_S0, BC_OPS, val_off);
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        (void)bc_ip;
        void *runtime = op == INSTR_MUT_ADD ? (void *)jit_rt_member_mut_add
                : op == INSTR_MUT_SUB ? (void *)jit_rt_member_mut_sub
                : op == INSTR_MUT_MUL ? (void *)jit_rt_member_mut_mul
                                      : (void *)jit_rt_member_mut_div;
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_LOC, ctx->param_count * VALUE_SIZE);
        jit_emit_load_imm(asm, BC_A2, member_id);
        jit_emit_add_imm(asm, BC_A3, BC_OPS, val_off);
        jit_emit_add_imm(asm, BC_A4, BC_OPS, val_off);
        jit_emit_load_imm(asm, BC_CALL, (iptr)runtime);
        bc_emit_reentrant_call(ctx, BC_CALL);
        jit_emit_label(asm, lbl_done);
        return true;
}

static void
bc_emit_trampoline_signal(JitCtx *ctx, int status, int idx)
{
        dasm_State **asm = &ctx->asm;

        // Load packed return value: (idx << 4) | reason
        i32 packed = JIT_PACK(status, idx);
        jit_emit_load_imm(asm, BC_RET, packed);

        // Jump to epilogue (restore regs + ret), preserving the return value
        jit_emit_jump_epilogue_restore(asm);
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

        if (V_TYPE(*(method)) != VALUE_FUNCTION) {
                return NULL;
        }

        return v_(cls->methods.values, method_idx);
}

static Value *
bc_resolve_getter(Class *cls, int member_id)
{
        if (member_id < 0 || member_id >= (int)vN(cls->offsets_r)) {
                return NULL;
        }
        u16 offset = v__(cls->offsets_r, member_id);
        if ((offset >> OFF_SHIFT) != OFF_GETTER) {
                return NULL;
        }
        int getter = offset & OFF_MASK;
        if (getter >= vN(cls->getters.values)) {
                return NULL;
        }
        Value *value = v_(cls->getters.values, getter);
        return V_TYPE(*(value)) == VALUE_FUNCTION ? value : NULL;
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

typedef struct {
        Class *class;
        u16 offset;
} BcInlineField;

static int
bc_inline_local_pos(TyInlinePlan const *plan, TyInlineKind kind, int base,
                    int self_pos, int local)
{
        if (local >= 0 && local < plan->argc) {
                return base + local;
        }
        if (kind == TY_INLINE_METHOD && local == plan->self_local) {
                return self_pos;
        }
        return -1;
}

static bool
bc_resolve_inline_fields(JitCtx *ctx, TyInlinePlan const *plan, TyInlineKind kind,
                         int base, int self_pos, Class *self_class,
                         BcInlineField fields[TY_INLINE_MAX_INSNS])
{
        for (int i = 0; i < plan->count; ++i) {
                TyInlineInsn const *insn = &plan->insns[i];
                if (insn->op != TY_INLINE_FIELD && insn->op != TY_INLINE_STORE_FIELD) {
                        continue;
                }

                int pos = bc_inline_local_pos(plan, kind, base, self_pos, insn->local);
                if (pos < 0 || pos >= MAX_BC_OPS) {
                        return false;
                }

                Class *class = kind == TY_INLINE_METHOD && insn->local == plan->self_local
                             ? self_class
                             : expected_class_of(ctx->ty, ctx->op_types[pos]);
                if (class == NULL || insn->member >= (int)vN(class->offsets_r)) {
                        return false;
                }

                u16 offset = v__(class->offsets_r, insn->member);
                if (offset == OFF_NOT_FOUND || (offset >> OFF_SHIFT) != OFF_FIELD) {
                        return false;
                }

                fields[i].class = class;
                fields[i].offset = offset;
        }

        return true;
}

static bool
bc_inline_plan_types(JitCtx *ctx, Value const *callee, TyInlinePlan const *plan)
{
        u8 root = plan->insns[plan->count - 1].op;
        bool control = false;
        bool numeric = false;
        for (int i = 0; i < plan->count; ++i) {
                u8 op = plan->insns[i].op;
                control |= op == TY_INLINE_BRANCH_TRUE
                        || op == TY_INLINE_JUMP;
                numeric |= op == TY_INLINE_ADD
                        || op == TY_INLINE_SUB
                        || op == TY_INLINE_MUL
                        || op == TY_INLINE_DIV
                        || op == TY_INLINE_EQ
                        || op == TY_INLINE_NE
                        || op == TY_INLINE_LT
                        || op == TY_INLINE_GT
                        || op == TY_INLINE_LE
                        || op == TY_INLINE_GE;
        }
        bool arithmetic = root == TY_INLINE_ADD
                       || root == TY_INLINE_SUB
                       || root == TY_INLINE_MUL
                       || root == TY_INLINE_DIV;
        bool comparison = root == TY_INLINE_EQ
                       || root == TY_INLINE_NE
                       || root == TY_INLINE_LT
                       || root == TY_INLINE_GT
                       || root == TY_INLINE_LE
                       || root == TY_INLINE_GE;
        if (!numeric) {
                return true;
        }

        Type *function = type_resolve_var(type_of(callee));
        if (!IsFuncT(function)) {
                return false;
        }
        Class *result = expected_class_of(ctx->ty, function->rt);
        if (result == NULL) {
                return false;
        }
        if (control) {
                return result->i == CLASS_INT
                    || result->i == CLASS_FLOAT
                    || result->i == CLASS_BOOL;
        }
        return arithmetic
             ? result->i == CLASS_INT || result->i == CLASS_FLOAT
             : comparison && result->i == CLASS_BOOL;
}

static void
bc_emit_inline_object_guard(JitCtx *ctx, int source_pos, Class const *class,
                            int lbl_slow)
{
        dasm_State **asm = &ctx->asm;
        int source_off = OP_OFF(source_pos);
        jit_emit_ldr64(asm, BC_S3, BC_OPS, source_off);
        jit_emit_decode_direct_object(asm, BC_S2, BC_S3, lbl_slow);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OBJ_OFF_CLASS);
        jit_emit_load_imm(asm, BC_S1, (iptr)class);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
        jit_emit_branch_ne(asm, lbl_slow);
}

static void
bc_emit_inline_layout_guard(JitCtx *ctx, int member,
                            BcInlineField const *field, int lbl_slow)
{
        dasm_State **asm = &ctx->asm;
        int items_off = (int)offsetof(Class, offsets_r)
                      + (int)offsetof(u16Vector, items);
        int count_off = (int)offsetof(Class, offsets_r)
                      + (int)offsetof(u16Vector, count);
        jit_emit_load_imm(asm, BC_S3, (iptr)field->class);
        jit_emit_ldr64(asm, BC_S0, BC_S3, count_off);
        jit_emit_load_imm(asm, BC_S1, member);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
        jit_emit_branch_ule(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S3, BC_S3, items_off);
        jit_emit_load_imm(asm, BC_S1, (i64)(u32)member * sizeof (u16));
        jit_emit_ldr16_index(asm, BC_S0, BC_S3, BC_S1);
        jit_emit_load_imm(asm, BC_S1, field->offset);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
        jit_emit_branch_ne(asm, lbl_slow);
}

static void
bc_emit_inline_field_load(JitCtx *ctx, int source_pos, int dest_pos,
                          BcInlineField const *field)
{
        dasm_State **asm = &ctx->asm;
        int source_off = OP_OFF(source_pos);
        int dest_off = OP_OFF(dest_pos);
        jit_emit_ldr64(asm, BC_S2, BC_OPS, source_off);
        jit_emit_strip_direct_pointer(asm, BC_S2, BC_S2);
        int slot_off = OBJ_OFF_SLOTS + (field->offset & OFF_MASK) * VALUE_SIZE;
        bc_copy_value(ctx, BC_OPS, dest_off, BC_S2, slot_off);
}

static void
bc_emit_inline_arithmetic(JitCtx *ctx, u8 op, int left, int right, int lbl_slow)
{
        dasm_State **asm = &ctx->asm;
        if (VALUE_SIZE == 8) {
                jit_emit_jump(asm, lbl_slow);
                return;
        }
        int lbl_left_int = bc_next_label(ctx);
        int lbl_int_int = bc_next_label(ctx);
        int lbl_real_real = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);

        jit_emit_ldrb(asm, BC_S0, BC_OPS, left + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_eq(asm, lbl_left_int);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_REAL);
        jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_ldrb(asm, BC_S0, BC_OPS, right + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_REAL);
        jit_emit_branch_eq(asm, lbl_real_real);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_farith_mixed(
                asm, BC_OPS, left + VAL_OFF_Z, right + VAL_OFF_Z,
                false, op - TY_INLINE_ADD
        );
        jit_emit_jump(asm, lbl_done);

        jit_emit_label(asm, lbl_real_real);
        if (op == TY_INLINE_ADD) {
                jit_emit_fadd(asm, BC_OPS, left + VAL_OFF_Z, right + VAL_OFF_Z);
        } else if (op == TY_INLINE_SUB) {
                jit_emit_fsub(asm, BC_OPS, left + VAL_OFF_Z, right + VAL_OFF_Z);
        } else {
                jit_emit_fmul(asm, BC_OPS, left + VAL_OFF_Z, right + VAL_OFF_Z);
        }
        jit_emit_jump(asm, lbl_done);

        jit_emit_label(asm, lbl_left_int);
        jit_emit_ldrb(asm, BC_S0, BC_OPS, right + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_eq(asm, lbl_int_int);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_REAL);
        jit_emit_branch_ne(asm, lbl_slow);
        jit_emit_farith_mixed(
                asm, BC_OPS, left + VAL_OFF_Z, right + VAL_OFF_Z,
                true, op - TY_INLINE_ADD
        );
        jit_emit_load_imm(asm, BC_S0, VALUE_REAL);
        jit_emit_strb(asm, BC_S0, BC_OPS, left + VAL_OFF_TYPE);
        jit_emit_jump(asm, lbl_done);

        jit_emit_label(asm, lbl_int_int);
        jit_emit_ldr64(asm, BC_S0, BC_OPS, left + VAL_OFF_Z);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, right + VAL_OFF_Z);
        if (op == TY_INLINE_ADD) {
                jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
        } else if (op == TY_INLINE_SUB) {
                jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
        } else {
                jit_emit_mul(asm, BC_S0, BC_S0, BC_S1);
        }
        jit_emit_str64(asm, BC_S0, BC_OPS, left + VAL_OFF_Z);
        jit_emit_label(asm, lbl_done);
}

static void
bc_emit_inline_mixed_comparison(JitCtx *ctx, u8 op, int left, int right,
                                bool left_int, int lbl_slow)
{
        dasm_State **asm = &ctx->asm;
        if (op == TY_INLINE_EQ || op == TY_INLINE_NE) {
                jit_emit_jump(asm, lbl_slow);
                return;
        }
        jit_emit_fcmp_mixed(
                asm, BC_S0, BC_S1, BC_OPS,
                left + VAL_OFF_Z, right + VAL_OFF_Z,
                left_int, op - TY_INLINE_EQ
        );
}

static void
bc_emit_inline_comparison(JitCtx *ctx, u8 op, int left, int right, int lbl_slow)
{
        dasm_State **asm = &ctx->asm;
        if (VALUE_SIZE == 8) {
                jit_emit_jump(asm, lbl_slow);
                return;
        }
        int lbl_left_real = bc_next_label(ctx);
        int lbl_int_int = bc_next_label(ctx);
        int lbl_real_real = bc_next_label(ctx);
        int lbl_mixed = bc_next_label(ctx);
        int lbl_mixed_left_int = bc_next_label(ctx);
        int lbl_float_compare = bc_next_label(ctx);
        int lbl_write = bc_next_label(ctx);

        jit_emit_ldr64(asm, BC_S0, BC_OPS, left);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, right);
        jit_emit_branch_not_int32(asm, BC_S0, lbl_left_real);
        jit_emit_branch_not_int32(asm, BC_S1, lbl_mixed_left_int);
        jit_emit_jump(asm, lbl_int_int);

        jit_emit_label(asm, lbl_left_real);
        jit_emit_branch_not_double(asm, BC_S0, lbl_slow);
        jit_emit_branch_not_double(asm, BC_S1, lbl_mixed);
        jit_emit_jump(asm, lbl_real_real);

        jit_emit_label(asm, lbl_mixed_left_int);
        jit_emit_branch_not_double(asm, BC_S1, lbl_slow);
        if (op == TY_INLINE_EQ || op == TY_INLINE_NE) {
                jit_emit_load_imm(asm, BC_S0, op == TY_INLINE_NE);
                jit_emit_jump(asm, lbl_write);
        }
        bc_decode_int32(ctx, BC_S0, BC_S0);
        jit_emit_int_to_double_bits(asm, BC_S0, BC_S0);
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_sub(asm, BC_S1, BC_S1, BC_S2);
        jit_emit_jump(asm, lbl_float_compare);

        jit_emit_label(asm, lbl_mixed);
        jit_emit_branch_not_int32(asm, BC_S1, lbl_slow);
        if (op == TY_INLINE_EQ || op == TY_INLINE_NE) {
                jit_emit_load_imm(asm, BC_S0, op == TY_INLINE_NE);
                jit_emit_jump(asm, lbl_write);
        }
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_sub(asm, BC_S0, BC_S0, BC_S2);
        bc_decode_int32(ctx, BC_S1, BC_S1);
        jit_emit_int_to_double_bits(asm, BC_S1, BC_S1);
        jit_emit_jump(asm, lbl_float_compare);

        jit_emit_label(asm, lbl_real_real);
        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
        jit_emit_sub(asm, BC_S0, BC_S0, BC_S2);
        jit_emit_sub(asm, BC_S1, BC_S1, BC_S2);

        jit_emit_label(asm, lbl_float_compare);
        jit_emit_str64(asm, BC_S0, BC_OPS, left);
        jit_emit_str64(asm, BC_S1, BC_OPS, right);
        if (op == TY_INLINE_EQ) {
                jit_emit_fcmp_eq(asm, BC_S0, BC_S1, BC_OPS,
                                 left, right);
        } else if (op == TY_INLINE_NE) {
                jit_emit_fcmp_ne(asm, BC_S0, BC_S1, BC_OPS,
                                 left, right);
        } else if (op == TY_INLINE_LT) {
                jit_emit_fcmp_lt(asm, BC_S0, BC_S1, BC_OPS,
                                 left, right);
        } else if (op == TY_INLINE_GT) {
                jit_emit_fcmp_gt(asm, BC_S0, BC_S1, BC_OPS,
                                 left, right);
        } else if (op == TY_INLINE_LE) {
                jit_emit_fcmp_le(asm, BC_S0, BC_S1, BC_OPS,
                                 left, right);
        } else {
                jit_emit_fcmp_ge(asm, BC_S0, BC_S1, BC_OPS,
                                 left, right);
        }
        jit_emit_jump(asm, lbl_write);

        jit_emit_label(asm, lbl_int_int);
        bc_decode_int32(ctx, BC_S0, BC_S0);
        bc_decode_int32(ctx, BC_S1, BC_S1);
        if (op == TY_INLINE_EQ) {
                jit_emit_cmp_eq(asm, BC_S0, BC_S0, BC_S1);
        } else if (op == TY_INLINE_NE) {
                jit_emit_cmp_ne(asm, BC_S0, BC_S0, BC_S1);
        } else if (op == TY_INLINE_LT) {
                jit_emit_cmp_lt(asm, BC_S0, BC_S0, BC_S1);
        } else if (op == TY_INLINE_GT) {
                jit_emit_cmp_gt(asm, BC_S0, BC_S0, BC_S1);
        } else if (op == TY_INLINE_LE) {
                jit_emit_cmp_le(asm, BC_S0, BC_S0, BC_S1);
        } else {
                jit_emit_cmp_ge(asm, BC_S0, BC_S0, BC_S1);
        }

        jit_emit_label(asm, lbl_write);
        bc_write_bool(ctx, left, BC_S0);
}

static bool
bc_emit_inline_plan(JitCtx *ctx, TyInlinePlan const *plan, TyInlineKind kind,
                    int base, int self_pos, int scratch, Class *self_class,
                    int lbl_slow)
{
        if (scratch + plan->max_stack > MAX_BC_OPS) {
                return false;
        }

        BcInlineField fields[TY_INLINE_MAX_INSNS] = {0};
        if (!bc_resolve_inline_fields(ctx, plan, kind, base, self_pos,
                                      self_class, fields)) {
                return false;
        }

        dasm_State **asm = &ctx->asm;
        for (int i = 0; i < plan->count; ++i) {
                TyInlineInsn const *insn = &plan->insns[i];
                if (insn->op != TY_INLINE_FIELD && insn->op != TY_INLINE_STORE_FIELD) {
                        continue;
                }
                int source = bc_inline_local_pos(
                        plan, kind, base, self_pos, insn->local
                );
                bool object_proven = kind == TY_INLINE_METHOD
                                  && insn->local == plan->self_local;
                bool layout_proven = false;
                for (int j = 0; j < i; ++j) {
                        TyInlineInsn const *previous = &plan->insns[j];
                        if (previous->op != TY_INLINE_FIELD && previous->op != TY_INLINE_STORE_FIELD) {
                                continue;
                        }
                        int previous_source = bc_inline_local_pos(
                                plan, kind, base, self_pos, previous->local
                        );
                        if (previous_source == source
                            && fields[j].class == fields[i].class) {
                                object_proven = true;
                        }
                        if (previous->member == insn->member
                            && fields[j].class == fields[i].class
                            && fields[j].offset == fields[i].offset) {
                                layout_proven = true;
                        }
                }
                if (!object_proven) {
                        bc_emit_inline_object_guard(
                                ctx, source, fields[i].class, lbl_slow
                        );
                }
                if (!layout_proven) {
                        bc_emit_inline_layout_guard(
                                ctx, insn->member, &fields[i], lbl_slow
                        );
                }
        }

        int labels[TY_INLINE_MAX_INSNS + 1];
        for (int i = 0; i <= plan->count; ++i) {
                labels[i] = -1;
        }
        for (int i = 0; i < plan->count; ++i) {
                TyInlineInsn const *insn = &plan->insns[i];
                if (insn->op == TY_INLINE_BRANCH_TRUE
                    || insn->op == TY_INLINE_JUMP) {
                        if (labels[insn->target] < 0) {
                                labels[insn->target] = bc_next_label(ctx);
                        }
                }
        }

        int depth = 0;
        for (int i = 0; i < plan->count; ++i) {
                if (labels[i] >= 0) {
                        jit_emit_label(asm, labels[i]);
                }
                depth = plan->depths[i];
                TyInlineInsn const *insn = &plan->insns[i];

                switch (insn->op) {
                case TY_INLINE_LOCAL:
                {
                        int source = bc_inline_local_pos(plan, kind, base, self_pos,
                                                         insn->local);
                        bc_copy_value(ctx, BC_OPS, OP_OFF(scratch + depth),
                                      BC_OPS, OP_OFF(source));
                        depth++;
                        break;
                }

                case TY_INLINE_FIELD:
                {
                        int source = bc_inline_local_pos(plan, kind, base, self_pos,
                                                         insn->local);
                        bc_emit_inline_field_load(
                                ctx, source, scratch + depth, &fields[i]
                        );
                        depth++;
                        break;
                }

                case TY_INLINE_BOOLEAN:
                        jit_emit_load_imm(asm, BC_S0, insn->integer ? NANBOX_VALUE_TRUE : NANBOX_VALUE_FALSE);
                        jit_emit_str64(asm, BC_S0, BC_OPS, OP_OFF(scratch + depth));
                        depth++;
                        break;

                case TY_INLINE_STORE_FIELD:
                {
                        int source = bc_inline_local_pos(plan, kind, base, self_pos, insn->local);
                        jit_emit_ldr64(asm, BC_S2, BC_OPS, OP_OFF(source));
                        jit_emit_strip_direct_pointer(asm, BC_S2, BC_S2);
                        jit_emit_load_imm(asm, BC_S0, insn->integer ? NANBOX_VALUE_TRUE : NANBOX_VALUE_FALSE);
                        int slot_off = OBJ_OFF_SLOTS + (fields[i].offset & OFF_MASK) * VALUE_SIZE;
                        jit_emit_str64(asm, BC_S0, BC_S2, slot_off);
                        jit_emit_str64(asm, BC_S0, BC_OPS, OP_OFF(scratch + depth));
                        depth++;
                        break;
                }

                case TY_INLINE_POP:
                        depth--;
                        break;

                case TY_INLINE_INTEGER:
                {
                        int off = OP_OFF(scratch + depth);
                        if (insn->integer < INT32_MIN || insn->integer > INT32_MAX) {
                                jit_emit_jump(asm, lbl_slow);
                                break;
                        }
                        jit_emit_load_imm(asm, BC_S0,
                                (i64)(NANBOX_MIN_NUMBER | (u32)(i32)insn->integer));
                        jit_emit_str64(asm, BC_S0, BC_OPS, off);
                        depth++;
                        break;
                }

                case TY_INLINE_REAL:
                {
                        int off = OP_OFF(scratch + depth);
                        u64 bits;
                        memcpy(&bits, &insn->real, sizeof bits);
                        bits += NANBOX_DOUBLE_ENCODE_OFFSET;
                        jit_emit_load_imm(asm, BC_S0, (i64)bits);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off);
                        depth++;
                        break;
                }

                case TY_INLINE_ADD:
                case TY_INLINE_SUB:
                case TY_INLINE_MUL:
                case TY_INLINE_DIV:
                {
                        int saved_sp = ctx->sp;
                        ctx->sp = scratch + depth;
                        void *helper = insn->op == TY_INLINE_ADD ? (void *)jit_rt_add
                                     : insn->op == TY_INLINE_SUB ? (void *)jit_rt_sub
                                     : insn->op == TY_INLINE_MUL ? (void *)jit_rt_mul
                                                                 : (void *)jit_rt_div;
                        bc_emit_arith(ctx, helper);
                        ctx->sp = saved_sp;
                        depth--;
                        break;
                }

                case TY_INLINE_EQ:
                case TY_INLINE_NE:
                case TY_INLINE_LT:
                case TY_INLINE_GT:
                case TY_INLINE_LE:
                case TY_INLINE_GE:
                {
                        int left = OP_OFF(scratch + depth - 2);
                        int right = OP_OFF(scratch + depth - 1);
                        bc_emit_inline_comparison(
                                ctx, insn->op, left, right, lbl_slow
                        );
                        depth--;
                        break;
                }

                case TY_INLINE_BRANCH_TRUE:
                        jit_emit_ldr64(
                                asm, BC_S0, BC_OPS, OP_OFF(scratch + depth - 1)
                        );
                        jit_emit_load_imm(asm, BC_S1, NANBOX_VALUE_TRUE);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
                        jit_emit_branch_eq(asm, labels[insn->target]);
                        break;

                case TY_INLINE_JUMP:
                        jit_emit_jump(asm, labels[insn->target]);
                        break;
                }
        }

        if (labels[plan->count] >= 0) {
                jit_emit_label(asm, labels[plan->count]);
        }
        depth = plan->depths[plan->count];
        if (depth != 1) {
                return false;
        }

        bc_copy_value(ctx, BC_OPS, OP_OFF(base), BC_OPS, OP_OFF(scratch));
        if (scratch + plan->max_stack > ctx->max_sp) {
                ctx->max_sp = scratch + plan->max_stack;
        }
        return true;
}

static bool
bc_emit_inline_getter(JitCtx *ctx, char const *op_ip, int member,
                      Class *receiver_class, Value const *getter)
{
        TyInlinePlan plan;
        if (!ty_inline_analyze(getter, TY_INLINE_METHOD, 0, &plan)
            || !bc_inline_plan_types(ctx, getter, &plan)
            || ctx->inline_cost + plan.count > TY_INLINE_MAX_COST) {
                return false;
        }

        int base = ctx->sp - 1;
        int self_pos = base;
        int scratch = ctx->sp;
        if (scratch + plan.max_stack > MAX_BC_OPS) {
                return false;
        }

        BcInlineField fields[TY_INLINE_MAX_INSNS] = {0};
        if (!bc_resolve_inline_fields(
                ctx, &plan, TY_INLINE_METHOD, base, self_pos,
                receiver_class, fields
        )) {
                return false;
        }

        ctx->inline_cost += plan.count;
        dasm_State **asm = &ctx->asm;
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);
        TyInlineTarget *target = ty_inline_getter_target(
                receiver_class, member, getter
        );

        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(self_pos));
        jit_emit_load_imm(asm, BC_A2, (iptr)target);
        jit_emit_load_imm(asm, BC_CALL, (iptr)ty_inline_guard_member);
        bc_emit_runtime_call(ctx, BC_CALL);
        jit_emit_cbz(asm, BC_RET, lbl_slow);

        bool emitted = bc_emit_inline_plan(
                ctx, &plan, TY_INLINE_METHOD, base, self_pos, scratch,
                receiver_class, lbl_slow
        );
        ASSERT(emitted);
        (void)emitted;
        EMIT_STAT(jit_rt_stat_member_fast);
        jit_emit_jump(asm, lbl_done);

        jit_emit_label(asm, lbl_slow);
        EMIT_SLOW1(op_ip, SLOW_MEMBER_ACCESS, BC_OPS, OP_OFF(base));
        jit_emit_mov(asm, BC_A0, BC_TY);
        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(base));
        jit_emit_mov(asm, BC_A2, BC_A1);
        jit_emit_load_imm(asm, BC_A3, member);
        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
        bc_emit_runtime_call(ctx, BC_CALL);

        jit_emit_label(asm, lbl_done);
        return true;
}

static int
jit_rt_double_math(Value *result, Value const *a, int op)
{
        if (!nanbox_is_double(a->bits)) return 0;
        double x = nanbox_to_double(a->bits);
        *result = value_real(op == 1 ? sin(x) : cos(x));
        return 1;
}

static int
jit_rt_double_max(Value *result, Value const *a, Value const *b)
{
        if (!nanbox_is_double(a->bits) || !nanbox_is_double(b->bits)) return 0;
        double x = nanbox_to_double(a->bits), y = nanbox_to_double(b->bits);
        int cmp = y < x ? -1 : y != x;
        *result = cmp > 0 ? *b : *a;
        return 1;
}



static void
bc_emit_inline_global_guard(JitCtx *ctx, int global, Value const *callee,
                            int lbl_slow)
{
        dasm_State **asm = &ctx->asm;
        jit_emit_load_imm(asm, BC_S2, (iptr)&Globals);
        jit_emit_ldr64(asm, BC_S0, BC_S2, OFF_VEC_LEN);
        jit_emit_load_imm(asm, BC_S1, global);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
        jit_emit_branch_ule(asm, lbl_slow);
        jit_emit_ldr64(asm, BC_S3, BC_S2, OFF_VEC_DATA);
        jit_emit_load_imm(asm, BC_S1, (iptr)global * sizeof (Value));
        jit_emit_add(asm, BC_S3, BC_S3, BC_S1);
        jit_emit_ldr64(asm, BC_S0, BC_S3, 0);
        jit_emit_load_imm(asm, BC_S1, (i64)callee->bits.as_int64);
        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
        jit_emit_branch_ne(asm, lbl_slow);
}

static int
bc_emit_inline_global(JitCtx *ctx, Value const *callee, int global, int argc)
{
        if (V_TYPE(*(callee)) != VALUE_FUNCTION || class_of(callee) != -1) {
                return -1;
        }
        TyInlinePlan plan;
        if (!ty_inline_analyze(callee, TY_INLINE_GLOBAL, argc, &plan)
            || !bc_inline_plan_types(ctx, callee, &plan)) {
                return -1;
        }

        int base = ctx->sp;
        int scratch = base + argc;
        BcInlineField fields[TY_INLINE_MAX_INSNS] = {0};
        if (ctx->inline_cost + plan.count > TY_INLINE_MAX_COST
            || scratch + plan.max_stack > MAX_BC_OPS
            || !bc_resolve_inline_fields(
                    ctx, &plan, TY_INLINE_GLOBAL, base, -1, NULL, fields
               )) {
                return -1;
        }

        ctx->inline_cost += plan.count;
        int lbl_slow = bc_next_label(ctx);
        int lbl_done = bc_next_label(ctx);
        dasm_State **asm = &ctx->asm;
        Symbol **globals = vv(*compiler_globals(ctx->ty));
        if (!SymbolIsConst(globals[global])) {
                bc_emit_inline_global_guard(ctx, global, callee, lbl_slow);
        }

        bool emitted = bc_emit_inline_plan(
                ctx, &plan, TY_INLINE_GLOBAL, base, -1, scratch, NULL, lbl_slow
        );
        ASSERT(emitted);
        (void)emitted;
        jit_emit_jump(asm, lbl_done);
        jit_emit_label(asm, lbl_slow);
        return lbl_done;
}

static bool
bc_emit_inline_operator(JitCtx *ctx, int op, void *fallback)
{
        (void)ctx;
        (void)op;
        (void)fallback;
        return false;
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

#if 1
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
        int inline_done = -1;

        if (baked_method != NULL && nkw == 0) {
                TyInlinePlan plan;
                if (ty_inline_analyze(baked_method, TY_INLINE_METHOD, n, &plan)
                    && bc_inline_plan_types(ctx, baked_method, &plan)) {
                        BcInlineField fields[TY_INLINE_MAX_INSNS] = {0};
                        bool supported = ctx->inline_cost + plan.count <= TY_INLINE_MAX_COST
                                      && ctx->sp + plan.max_stack <= MAX_BC_OPS
                                      && bc_resolve_inline_fields(
                                                ctx, &plan, TY_INLINE_METHOD,
                                                ctx->sp - 1 - n, ctx->sp - 1,
                                                recv_cls, fields
                                         );
                        if (supported) {
                                ctx->inline_cost += plan.count;
                                int inline_slow = bc_next_label(ctx);
                                inline_done = bc_next_label(ctx);
                                TyInlineTarget *target = ty_inline_method_target(
                                        recv_cls, z, baked_method
                                );

                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, self_off);
                                jit_emit_load_imm(asm, BC_A2, (iptr)target);
                                jit_emit_load_imm(asm, BC_CALL,
                                                  (iptr)ty_inline_guard_member);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                jit_emit_cbz(asm, BC_RET, inline_slow);

                                bool emitted = bc_emit_inline_plan(
                                        ctx, &plan, TY_INLINE_METHOD,
                                        ctx->sp - 1 - n, ctx->sp - 1, ctx->sp,
                                        recv_cls, inline_slow
                                );
                                ASSERT(emitted);
                                (void)emitted;
                                jit_emit_jump(asm, inline_done);
                                jit_emit_label(asm, inline_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);
                                jit_emit_load_imm(asm, BC_A3, z);
                                jit_emit_load_imm(asm, BC_A4, n);
                                jit_emit_load_imm(asm, BC_CALL,
                                                  (iptr)jit_rt_call_method);
                                bc_emit_runtime_call(ctx, BC_CALL);
                        }
                }
        }

        if (inline_done < 0) {
                if (builtin_method != NULL) {
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);
                        jit_emit_load_imm(asm, BC_A3, (iptr)builtin_method);
                        jit_emit_load_imm(asm, BC_A4, PACK32(builtin_vtype, z));
                        jit_emit_load_imm(asm, BC_A5, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_builtin_method);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        DBG("CALL_METHOD (builtin fast path for %s)", M_NAME(z));
                } else if (baked_method != NULL) {
                        bool can_tramp = (rest_idx_of(baked_method) == -1)
                                      && (kwargs_idx_of(baked_method) == -1)
                                      && !is_starred(baked_method);
                        if (can_tramp) {
                                jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp - 1);

                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, self_off);
                                jit_emit_load_imm(asm, BC_A2, (iptr)baked_method);
                                jit_emit_load_imm(asm, BC_A3, recv_cls->i);
                                jit_emit_load_imm(asm, BC_A4, n);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_baked_call);
                                bc_emit_runtime_call(ctx, BC_CALL);

                                int lbl_cm_done = bc_next_label(ctx);
                                int lbl_cm_fallback = bc_next_label(ctx);

                                jit_emit_cbz(asm, BC_RET, lbl_cm_fallback);
                                jit_emit_cmp_ri(asm, BC_RET, 2);
                                jit_emit_branch_ne(asm, lbl_cm_done);
                                jit_emit_reload_stack(asm, ctx->bound);
                                jit_emit_jump(asm, lbl_cm_done);

                                jit_emit_label(asm, lbl_cm_fallback);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);
                                jit_emit_load_imm(asm, BC_A3, (iptr)baked_method);
                                jit_emit_load_imm(asm, BC_A4, PACK32(recv_cls->i, z));
                                jit_emit_load_imm(asm, BC_A5, n);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_self_method_guarded);
                                bc_emit_runtime_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_cm_done);
                                DBG("CALL_METHOD (baked trampoline for %s)", M_NAME(z));
                        } else {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);
                                jit_emit_load_imm(asm, BC_A3, (iptr)baked_method);
                                jit_emit_load_imm(asm, BC_A4, PACK32(recv_cls->i, z));
                                jit_emit_load_imm(asm, BC_A5, n);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_self_method_guarded);
                                bc_emit_runtime_call(ctx, BC_CALL);
                        }
                } else {
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, self_off);
                        jit_emit_load_imm(asm, BC_A3, z);
                        jit_emit_load_imm(asm, BC_A4, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_method);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        DBG("CALL_METHOD (generic fast path)");
                }
        }

        if (inline_done >= 0) {
                jit_emit_label(asm, inline_done);
        }

        // Pop self + n args, push result
        ctx->sp -= n; // was n+1 slots (args+self), now 1 slot (result)

        DBG("CALL_METHOD[%s]", M_NAME(z));
}


static bool
bc_preserves_stack_base(u8 op)
{
        switch (op) {
        case INSTR_NOP:
        case INSTR_DUP:
        case INSTR_POP:
        case INSTR_POP2:
        case INSTR_SWAP:
        case INSTR_LOAD_LOCAL:
        case INSTR_LOAD_REF:
        case INSTR_LOAD_CAPTURED:
        case INSTR_ASSIGN_LOCAL:
        case INSTR_INTEGER:
        case INSTR_REAL:
        case INSTR_STRING:
        case INSTR_VALUE:
        case INSTR_TYPE:
        case INSTR_REGEX:
        case INSTR_TRUE:
        case INSTR_FALSE:
        case INSTR_NIL:
        case INSTR_NONE:
        case INSTR_SENTINEL:
        case INSTR_LOAD_GLOBAL:
        case INSTR_DUP2_SWAP:
        case INSTR_CLEAR_RC:
        case INSTR_PUSH_INDEX:

        /* Operator slow paths restore BC_OPS before rejoining. */
        case INSTR_ADD:
        case INSTR_SUB:
        case INSTR_MUL:
        case INSTR_DIV:
        case INSTR_MOD:
        case INSTR_BIT_AND:
        case INSTR_BIT_OR:
        case INSTR_BIT_XOR:
        case INSTR_SHL:
        case INSTR_SHR:
        case INSTR_NEG:
        case INSTR_NOT:
        case INSTR_EQ:
        case INSTR_NEQ:
        case INSTR_LT:
        case INSTR_GT:
        case INSTR_LEQ:
        case INSTR_GEQ:
        case INSTR_CMP:
        case INSTR_COUNT:
        case INSTR_INC:
        case INSTR_DEC:
        case INSTR_BINARY_OP:
        case INSTR_JEQ:
        case INSTR_JNE:
        case INSTR_JLT:
        case INSTR_JGT:
        case INSTR_JLE:
        case INSTR_JGE:
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
        case INSTR_POST_INC:
        case INSTR_POST_DEC:
        case INSTR_PRE_INC:
        case INSTR_PRE_DEC:
                return true;
        default:
                return false;
        }
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
        bool stack_base_valid = false;

        DBG("=========== BEGIN ============");

        while (ip < end) {
                int off = (int)(ip - code);
                if (off >= 0 && off <= code_size) {
                        ctx->raw_dirty = ctx->cfg_dirty[off];
                }

                Type *hint0 = find_type_hint(hints, off);
                if (hint0 != NULL) {
                        ctx->op_types[ctx->sp - 1] = hint0;
#if JIT_SCAN_LOG
                        Expr const *e = compiler_find_expr(ty, code + off);
                        LOGX("[jit:%d] [%12.12s:%d] [%16.16s] hint at offset %d: %s",
                                ctx->sp,
                                e ? e->mod->path : "??",
                                e ? e->start.line + 1 : 0,
                                name_of(ctx->func),
                                off,
                                type_show(ty, hint0));
#endif
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
                        stack_base_valid = false;
                        jit_emit_label(asm, lbl);
                }

#ifdef TY_PROFILER
                bc_emit_profiler_tick_at(ctx, code + off);
                stack_base_valid = false;
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
                        if (!stack_base_valid) {
                                DBG("reloading stack before op %d (%s)", op, GetInstructionName(op));
                                jit_emit_reload_stack(asm, ctx->bound);
                                stack_base_valid = true;
                        }
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
                        if (bc_try_local_array_swap(ctx, code, end, &ip, locals, off, n)) {
                                break;
                        }
                        if (bc_try_local_array_get_assign(
                                    ctx, code, end, &ip, locals, off, n
                               )) {
                                break;
                        }
                        if (bc_try_local_array_store_pop(
                                    ctx, code, end, &ip, locals, off, n
                               )) {
                                break;
                        }
                        if (bc_try_local_array_get(
                                    ctx, code, end, &ip, locals, off, n
                               )) {
                                break;
                        }
                        if (bc_try_local_condition(
                                    ctx, code, end, &ip, locals, off, n
                               )) {
                                break;
                        }
                        if (bc_try_local_subscript(
                                    ctx, code, end, &ip, locals, off, n
                               )) {
                                break;
                        }
                        if (bc_try_local_int_jcmp(
                                    ctx, code, end, &ip, locals, off, n
                               )) {
                                break;
                        }
                        char const *q = ip;
                        if (n >= 0
                            && n < ctx->bound
                            && q + 1 + sizeof(int) + 2 <= end
                            && (u8)*q == INSTR_TARGET_LOCAL) {
                                int target;
                                int target_offset = (int)(q - code);
                                ++q;
                                __builtin_memcpy(&target, q, sizeof target);
                                q += sizeof target;
                                int mut_offset = (int)(q - code);
                                u8 mut = (u8)*q++;
                                int pop_offset = (int)(q - code);
                                Class *source_class = expected_class_of(
                                        ctx->ty, locals[n]->type
                                );
                                Class *target_class = target >= 0 && target < ctx->bound
                                        ? expected_class_of(ctx->ty, locals[target]->type)
                                        : NULL;
                                if ((mut == INSTR_MUT_ADD
                                     || mut == INSTR_MUT_SUB
                                     || mut == INSTR_MUT_MUL)
                                    && (u8)*q == INSTR_POP
                                    && source_class != NULL
                                    && target_class != NULL
                                    && source_class->i == target_class->i
                                    && source_class->i == CLASS_INT
                                    && bc_find_label(ctx, target_offset) < 0
                                    && bc_find_label(ctx, mut_offset) < 0
                                    && bc_find_label(ctx, pop_offset) < 0
                                    && bc_cfg_same_block(
                                            ctx, target_offset, mut_offset, pop_offset
                                    )) {
#ifdef TY_PROFILER
                                        bc_emit_profiler_tick_at(ctx, code + target_offset);
                                        bc_emit_profiler_tick_at(ctx, code + mut_offset);
                                        bc_emit_profiler_tick_at(ctx, code + pop_offset);
#endif
                                        bc_emit_numeric_mut(
                                                ctx, BC_LOC, n * VALUE_SIZE,
                                                true, false, target, mut, source_class->i
                                        );
                                        ip = q + 1;
                                        break;
                                }
                        }
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
                        bc_raw_kill(ctx, n);
                        break;
                }

                CASE(TARGET_LOCAL) {
                        int n;
                        BC_READ(n);
                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++;
                                bc_copy_value(ctx, BC_LOC, n * VALUE_SIZE,
                                              BC_OPS, OP_OFF(ctx->sp - 1));
                                bc_raw_kill(ctx, n);
                        } else if (ip < end && ((u8)*ip == INSTR_MUT_ADD
                                             || (u8)*ip == INSTR_MUT_SUB
                                             || (u8)*ip == INSTR_MUT_MUL
                                             || (u8)*ip == INSTR_MUT_DIV
                                             || (u8)*ip == INSTR_MUT_MOD)) {
                                ctx->tgt_kind = TGT_LOCAL;
                                ctx->tgt_index = n;
                        } else {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, n * VALUE_SIZE);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_push_target);
                                bc_emit_runtime_call(ctx, BC_CALL);
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
                        i8 k = (i8)*ip++;
                        if (bc_try_local_int_imm_mut_pop(
                                ctx, code, end, &ip, locals, k
                        )) {
                                break;
                        }

                        // Fusion: INT8 k + SUBSCRIPT => constant-index subscript
                        if (
                                ctx->registerize
                             && (k >= 0)
                             && (ip < end)
                             && ((u8)*ip == INSTR_SUBSCRIPT)
                             && (bc_find_label(ctx, off + 2) == -1)
                        ) {
                                Type *t_con = type_resolve_var(ctx->op_types[ctx->sp - 1]);
                                Class *c = expected_class_of(ctx->ty, t_con);

                                /* This fusion still addresses the removed
                                 * 32-byte inline Value layout.  Direct tuples
                                 * use the ordinary subscript path below. */
                                if (VALUE_SIZE != 8 && c != NULL && c->i == CLASS_TUPLE) {
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
                        jit_emit_load_imm(asm, BC_S1, 0);
                        jit_emit_load_imm(asm, BC_S2, 0);
                        jit_emit_load_imm(asm, BC_S3, 0);
                                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, int_off);
                                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, int_off + 16);
                                        jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_strb(asm, BC_S0, BC_OPS, int_off + VAL_OFF_TYPE);
                                        jit_emit_load_imm(asm, BC_S0, k);
                                        jit_emit_str64(asm, BC_S0, BC_OPS, int_off + VAL_OFF_Z);
                                        jit_emit_mov(asm, BC_A0, BC_TY);
                                        jit_emit_add_imm(asm, BC_A1, BC_OPS, con_off);
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_subscript);
                                        bc_emit_runtime_call(ctx, BC_CALL);

                                        jit_emit_label(asm, lbl_done);
                                        // sp unchanged: container replaced by result, no int pushed
                                        break;
                                }

                                // Again for Array
                                if (VALUE_SIZE != 8 && c != NULL && c->i == CLASS_ARRAY) {
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
                                        bc_emit_runtime_call(ctx, BC_CALL);

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
                        if (bc_try_local_int_imm_mut_pop(
                                ctx, code, end, &ip, locals, k
                        )) {
                                break;
                        }
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
                        Value value = value_box(ctx->ty, (ValuePayload){ .type=VALUE_SENTINEL });
                        gc_immortalize(ctx->ty, &value);
                        bc_push_bits(ctx, value.bits.as_int64, NULL);
                        break;
                }

                CASE(NONE) {
                        int dst = OP_OFF(ctx->sp);
                        jit_emit_load_imm(asm, BC_S0, (i64)NANBOX_VALUE_UNDEFINED);
                        jit_emit_str64(asm, BC_S0, BC_OPS, dst);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(OPERATOR) {
                        int u_op;
                        int b_op;
                        BC_READ(u_op);
                        BC_READ(b_op);
                        Value value = value_box(ctx->ty, (ValuePayload){
                                .type=VALUE_OPERATOR, .uop=u_op, .bop=b_op
                        });
                        gc_immortalize(ctx->ty, &value);
                        bc_push_bits(ctx, value.bits.as_int64, NULL);
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
                        ctx->op_types[ctx->sp] = ctx->op_types[ctx->sp - 1];
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;

                CASE(SWAP) {
                        int a = OP_OFF(ctx->sp - 1);
                        int b = OP_OFF(ctx->sp - 2);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, a);
                        jit_emit_ldr64(asm, BC_S1, BC_OPS, b);
                        jit_emit_str64(asm, BC_S1, BC_OPS, a);
                        jit_emit_str64(asm, BC_S0, BC_OPS, b);
                        SWAP(Type *, ctx->op_types[ctx->sp - 1], ctx->op_types[ctx->sp - 2]);
                        break;
                }

                CASE(ADD)
                        if (!bc_emit_inline_operator(ctx, OP_ADD, (void *)jit_rt_add)) {
                                bc_emit_arith(ctx, (void *)jit_rt_add);
                        }
                        break;

                CASE(SUB)
                        if (!bc_emit_inline_operator(ctx, OP_SUB, (void *)jit_rt_sub)) {
                                bc_emit_arith(ctx, (void *)jit_rt_sub);
                        }
                        break;

                CASE(MUL)
                        if (!bc_emit_inline_operator(ctx, OP_MUL, (void *)jit_rt_mul)) {
                                bc_emit_arith(ctx, (void *)jit_rt_mul);
                        }
                        break;

                CASE(DIV)
                        bc_emit_arith(ctx, (void *)jit_rt_div);
                        break;

                CASE(MOD)
                        bc_emit_arith(ctx, (void *)jit_rt_mod);
                        break;

                CASE(NEG)
                        bc_emit_unop_helper(ctx, (void *)jit_rt_neg);
                        break;

                CASE(NOT)
                        bc_emit_unop_helper(ctx, (void *)jit_rt_not);
                        break;

                CASE(EQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_eq);
                        break;

                CASE(NEQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_ne);
                        break;

                CASE(LT)
                        if (!bc_emit_inline_operator(ctx, OP_LT, (void *)jit_rt_lt)) {
                                bc_emit_cmp(ctx, (void *)jit_rt_lt);
                        }
                        break;

                CASE(GT)
                        if (!bc_emit_inline_operator(ctx, OP_GT, (void *)jit_rt_gt)) {
                                bc_emit_cmp(ctx, (void *)jit_rt_gt);
                        }
                        break;

                CASE(LEQ)
                        if (!bc_emit_inline_operator(ctx, OP_LEQ, (void *)jit_rt_le)) {
                                bc_emit_cmp(ctx, (void *)jit_rt_le);
                        }
                        break;

                CASE(GEQ)
                        if (!bc_emit_inline_operator(ctx, OP_GEQ, (void *)jit_rt_ge)) {
                                bc_emit_cmp(ctx, (void *)jit_rt_ge);
                        }
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
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp - 1));
                        jit_emit_load_imm(asm, BC_S1, NIL.bits.as_int64);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
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
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_S1, NANBOX_VALUE_UNDEFINED);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
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
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid equality jump target");
                        bc_emit_binop_helper(ctx, op == INSTR_JEQ
                                ? (void *)jit_rt_eq : (void *)jit_rt_ne);
                        bc_emit_truthy(ctx);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_cbnz(asm, BC_S0, lbl_target);
                        break;
                }

                CASE(JLT)
                CASE(JGT)
                CASE(JLE)
                CASE(JGE) {
                        int n;
                        BC_READ(n);
                        IRQ_CHECK(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid relational jump target");
                        void *helper = op == INSTR_JLT ? (void *)jit_rt_lt
                                     : op == INSTR_JGT ? (void *)jit_rt_gt
                                     : op == INSTR_JLE ? (void *)jit_rt_le
                                     :                       (void *)jit_rt_ge;
                        int left_off = OP_OFF(ctx->sp - 2), right_off = OP_OFF(ctx->sp - 1);
                        int lbl_cmp_float = bc_next_label(ctx);
                        int lbl_cmp_slow = bc_next_label(ctx), lbl_cmp_done = bc_next_label(ctx);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, left_off);
                        jit_emit_ldr64(asm, BC_S1, BC_OPS, right_off);
                        jit_emit_branch_not_int32(asm, BC_S0, lbl_cmp_float);
                        jit_emit_branch_not_int32(asm, BC_S1, lbl_cmp_slow);
                        bc_decode_int32(ctx, BC_S0, BC_S0);
                        bc_decode_int32(ctx, BC_S1, BC_S1);
                        if (op == INSTR_JLT) jit_emit_cmp_lt(asm, BC_S0, BC_S0, BC_S1);
                        else if (op == INSTR_JGT) jit_emit_cmp_gt(asm, BC_S0, BC_S0, BC_S1);
                        else if (op == INSTR_JLE) jit_emit_cmp_le(asm, BC_S0, BC_S0, BC_S1);
                        else jit_emit_cmp_ge(asm, BC_S0, BC_S0, BC_S1);
                        jit_emit_jump(asm, lbl_cmp_done);
                        jit_emit_label(asm, lbl_cmp_float);
                        jit_emit_branch_not_double(asm, BC_S0, lbl_cmp_slow);
                        jit_emit_branch_not_double(asm, BC_S1, lbl_cmp_slow);
                        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S2);
                        jit_emit_sub(asm, BC_S1, BC_S1, BC_S2);
                        int fa = OP_OFF(ctx->sp), fb = OP_OFF(ctx->sp + 1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, fa);
                        jit_emit_str64(asm, BC_S1, BC_OPS, fb);
                        if (op == INSTR_JLT) jit_emit_fcmp_lt(asm, BC_S0, BC_S1, BC_OPS, fa, fb);
                        else if (op == INSTR_JGT) jit_emit_fcmp_gt(asm, BC_S0, BC_S1, BC_OPS, fa, fb);
                        else if (op == INSTR_JLE) jit_emit_fcmp_le(asm, BC_S0, BC_S1, BC_OPS, fa, fb);
                        else jit_emit_fcmp_ge(asm, BC_S0, BC_S1, BC_OPS, fa, fb);
                        jit_emit_jump(asm, lbl_cmp_done);
                        jit_emit_label(asm, lbl_cmp_slow);
                        bc_emit_binop_helper(ctx, helper);
                        bc_emit_truthy(ctx);
                        jit_emit_label(asm, lbl_cmp_done);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_cbnz(asm, BC_S0, lbl_target);
                        break;
                }

                CASE(MEMBER_ACCESS) {
                        int z;
                        BC_READ(z);
                        Class *known = expected_class_of(ctx->ty, ctx->op_types[ctx->sp - 1]);
                        InternEntry const *member_name = intern_entry(&xD.members, z);
                        if (bc_emit_primitive_member(ctx, z, member_name->name)) break;
                        if (strcmp(member_name->name, "sqrt") == 0) {
                                int value_off = OP_OFF(ctx->sp - 1);
                                int lbl_slow_sqrt = bc_next_label(ctx);
                                int lbl_done_sqrt = bc_next_label(ctx);
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, value_off);
                                jit_emit_branch_not_double(asm, BC_S0, lbl_slow_sqrt);
                                jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_DOUBLE_ENCODE_OFFSET);
                                jit_emit_sub(asm, BC_S0, BC_S0, BC_S2);
                                jit_emit_fsqrt_bits(asm, BC_S0, BC_S0);
                                jit_emit_add(asm, BC_S0, BC_S0, BC_S2);
                                jit_emit_str64(asm, BC_S0, BC_OPS, value_off);
                                jit_emit_jump(asm, lbl_done_sqrt);
                                jit_emit_label(asm, lbl_slow_sqrt);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, value_off);
                                jit_emit_mov(asm, BC_A2, BC_A1);
                                jit_emit_load_imm(asm, BC_A3, z);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                                jit_emit_label(asm, lbl_done_sqrt);
                                break;
                        }
                        if (bc_emit_member_read_fast(ctx, z, ip)) break;
                        bc_emit_member_read_dynamic(ctx, z, ip);
                        break;
                }

                CASE(TRY_MEMBER_ACCESS) {
                        int z;
                        BC_READ(z);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A2, z);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_member);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        break;
                }

                CASE(SELF_MEMBER_ACCESS) {
                        int z;
                        BC_READ(z);
                        if (bc_emit_self_member_read_fast(ctx, z, code + off)) break;
                        int result = OP_OFF(ctx->sp++);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result);
                        jit_emit_load_imm(asm, BC_A2, 0);
                        jit_emit_load_imm(asm, BC_A3, z);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member);
                        bc_emit_reentrant_call(ctx, BC_CALL);
                        break;
                }

                CASE(GET_MEMBER) {
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_get_member);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        ctx->sp--;
                        break;
                }

                CASE(TARGET_MEMBER) {
                        int z;
                        BC_READ(z);
                        if (ip >= end) BAIL("deferred member target unsupported");
                        u8 next = (u8)*ip++;
                        int obj = OP_OFF(ctx->sp - 1);
                        int val = OP_OFF(ctx->sp - 2);
                        if (next == INSTR_ASSIGN) {
                                bc_emit_member_write_dynamic(ctx, z, code + off);
                                break;
                        }
                        if (next != INSTR_ASSIGN
                            && bc_emit_member_mut_fast(ctx, z, next, ip)) {
                                ctx->sp--;
                                break;
                        }
                        if (next == INSTR_ASSIGN) {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, obj);
                                jit_emit_load_imm(asm, BC_A2, z);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, val);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member_set);
                        } else if (next == INSTR_MUT_ADD || next == INSTR_MUT_SUB
                                   || next == INSTR_MUT_MUL || next == INSTR_MUT_DIV
                                   || next == INSTR_MUT_MOD) {
                                void *runtime = next == INSTR_MUT_ADD ? (void *)jit_rt_member_mut_add
                                        : next == INSTR_MUT_SUB ? (void *)jit_rt_member_mut_sub
                                        : next == INSTR_MUT_MUL ? (void *)jit_rt_member_mut_mul
                                        : next == INSTR_MUT_DIV ? (void *)jit_rt_member_mut_div
                                                                : (void *)jit_rt_member_mut_mod;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, obj);
                                jit_emit_load_imm(asm, BC_A2, z);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, val);
                                jit_emit_add_imm(asm, BC_A4, BC_OPS, val);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)runtime);
                        } else {
                                BAIL("deferred member target unsupported");
                        }
                        bc_emit_reentrant_call(ctx, BC_CALL);
                        ctx->sp--;
                        break;
                }

                CASE(TARGET_SELF_MEMBER) {
                        int z;
                        BC_READ(z);
                        if (ip >= end) BAIL("deferred self-member target unsupported");
                        u8 next = (u8)*ip++;
                        int val = OP_OFF(ctx->sp - 1);
                        if (next == INSTR_ASSIGN
                            && bc_emit_self_member_write_fast(ctx, z, code + off)) {
                                break;
                        }
                        if (next != INSTR_ASSIGN
                            && bc_emit_self_member_mut_fast(ctx, z, next, code + off)) {
                                break;
                        }
                        if (next == INSTR_ASSIGN) {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_load_imm(asm, BC_A1, 0);
                                jit_emit_load_imm(asm, BC_A2, z);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, val);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_member_set);
                        } else if (next == INSTR_MUT_ADD || next == INSTR_MUT_SUB
                                   || next == INSTR_MUT_MUL || next == INSTR_MUT_DIV
                                   || next == INSTR_MUT_MOD) {
                                void *runtime = next == INSTR_MUT_ADD ? (void *)jit_rt_member_mut_add
                                        : next == INSTR_MUT_SUB ? (void *)jit_rt_member_mut_sub
                                        : next == INSTR_MUT_MUL ? (void *)jit_rt_member_mut_mul
                                        : next == INSTR_MUT_DIV ? (void *)jit_rt_member_mut_div
                                                                : (void *)jit_rt_member_mut_mod;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, ctx->param_count * VALUE_SIZE);
                                jit_emit_load_imm(asm, BC_A2, z);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, val);
                                jit_emit_add_imm(asm, BC_A4, BC_OPS, val);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)runtime);
                        } else {
                                BAIL("deferred self-member target unsupported");
                        }
                        bc_emit_reentrant_call(ctx, BC_CALL);
                        break;
                }

                CASE(TARGET_SUBSCRIPT) {
                        // Stack: [..., container, subscript] -> pops both
                        // Record for deferred mutation
                        ctx->tgt_kind = TGT_SUBSCRIPT;
                        ctx->tgt_obj_sp = ctx->sp - 2; // container position
                        ctx->tgt_index  = ctx->sp - 1;  // subscript position (reusing field)
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
                        char const *kw_ip = (char const *)ip;
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (n == -1) {
                                BAIL("CALL with spread args not supported");
                        }

                        if (nkw > 0) {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_A2, n);
                                jit_emit_load_imm(asm, BC_A3, nkw);
                                jit_emit_load_imm(asm, BC_A4, (iptr)kw_ip);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_kw);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                ctx->sp -= n + nkw;
                                break;
                        }

                        Type *f0 = ctx->op_types[ctx->sp - 1];

                        DBG("CALL(argc=%d)", n);

                        // fn is still at ops[sp-1]
                        // Result overwrites the fn slot, args+fn all consumed => sp -= (n+1), push result => sp += 1
                        int fn_off = OP_OFF(ctx->sp - 1);
                        int out_off = OP_OFF(ctx->sp - 1 - n);
                        int known_class = ctx->op_known_class[ctx->sp - 1];

                        bool tail_position = false;
                        if (ip + 1 + sizeof(i32) <= end && (u8)*ip == INSTR_JUMP) {
                                i32 rel;
                                __builtin_memcpy(&rel, ip + 1, sizeof rel);
                                char const *target = ip + 1 + sizeof(i32) + rel;
                                tail_position = target >= code && target < end
                                             && (u8)*target == INSTR_RETURN;
                        }

                        // Sync the Ty stack count so helpers can set up callee frames.
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);

                        if (tail_position) {
                                int not_self_tail = bc_next_label(ctx);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, out_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, fn_off);
                                jit_emit_load_imm(asm, BC_A3, n);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_fast_self_tail);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                jit_emit_cbz(asm, BC_RET, not_self_tail);
                                jit_emit_jump(asm, bc_label_for(ctx, 0));
                                jit_emit_label(asm, not_self_tail);
                        }

                        // Direct self recursion is common in nested local functions.  Run
                        // it synchronously when the exact current function is called.
                        int lbl_slow_call = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);
                        u64 ctor_map;
                        bool ctor_nil_guard;
                        if (known_class > 0 && jit_simple_ctor_plan(ty, known_class, n,
                                                                  &ctor_map, &ctor_nil_guard)) {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, out_off);
                                jit_emit_load_imm(asm, BC_A2, known_class);
                                jit_emit_load_imm(asm, BC_A3, n);
                                jit_emit_load_imm(asm, BC_A4, (i64)ctor_map);
                                jit_emit_load_imm(asm, BC_A5, ctor_nil_guard);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_simple_ctor);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                jit_emit_reload_stack(asm, ctx->bound);
                                jit_emit_cmp_ri(asm, BC_RET, 1);
                                jit_emit_branch_eq(asm, lbl_done);
                        }
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, out_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, fn_off);
                        jit_emit_load_imm(asm, BC_A3, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_fast_self_call);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_cbz(asm, BC_RET, lbl_slow_call);
                        jit_emit_cmp_ri(asm, BC_RET, 2);
                        jit_emit_branch_ne(asm, lbl_done);
                        jit_emit_reload_stack(asm, ctx->bound);
                        jit_emit_jump(asm, lbl_done);

                        jit_emit_label(asm, lbl_slow_call);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, out_off);
                        jit_emit_add_imm(asm, BC_A2, BC_OPS, fn_off);
                        jit_emit_load_imm(asm, BC_A3, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_trampoline);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        /* Calls may grow/reallocate the VM operand stack. */
                        jit_emit_reload_stack(asm, ctx->bound);
                        jit_emit_cbz(asm, BC_RET, lbl_done);

                        // JIT callee detected: save resume index, signal trampoline, return
                        int site_idx = ctx->call_site_count++;
                        int resume_lbl = bc_next_label(ctx);
                        ctx->resume_labels[site_idx] = resume_lbl;

                        bc_emit_trampoline_signal(ctx, JIT_CALL, site_idx + 1);

                        // Resume label: entered when trampoline re-invokes us
                        // The callee's result is already on the Ty stack at the correct position.
                        // Registers will be reloaded at the next instruction's top-of-loop reload.
                        jit_emit_label(asm, resume_lbl);
                        bc_raw_reset(ctx);

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
                        char const *kw_ip = (char const *)ip;
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (n == -1) {
                                BAIL("CALL_METHOD with spread not supported");
                        }

                        if (nkw > 0) {
                                EMIT_SET_CALL_IP(op_ip);
                                ctx->sp -= n + nkw + 1;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp + n + nkw + 1));
                                jit_emit_load_imm(asm, BC_A2, z);
                                jit_emit_load_imm(asm, BC_A3, n);
                                jit_emit_load_imm(asm, BC_A4, nkw);
                                jit_emit_load_imm(asm, BC_A5, (iptr)kw_ip);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_method_kw);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                ctx->sp++;
                                if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                                break;
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
                        int inline_done = -1;

                        if (baked_method != NULL && ctx->self_class != NULL) {
                                TyInlinePlan plan;
                                if (ty_inline_analyze(
                                        baked_method, TY_INLINE_METHOD, n, &plan
                                ) && bc_inline_plan_types(ctx, baked_method, &plan)) {
                                        int base = ctx->sp - n;
                                        int self_pos = ctx->sp;
                                        int scratch = ctx->sp + 1;
                                        BcInlineField fields[TY_INLINE_MAX_INSNS] = {0};
                                        bool supported = ctx->inline_cost + plan.count <= TY_INLINE_MAX_COST
                                                      && scratch + plan.max_stack <= MAX_BC_OPS
                                                      && bc_resolve_inline_fields(
                                                                ctx, &plan, TY_INLINE_METHOD,
                                                                base, self_pos, ctx->self_class,
                                                                fields
                                                         );
                                        if (supported) {
                                                ctx->inline_cost += plan.count;
                                                int inline_slow = bc_next_label(ctx);
                                                inline_done = bc_next_label(ctx);
                                                TyInlineTarget *target = ty_inline_method_target(
                                                        ctx->self_class, z, baked_method
                                                );

                                                bc_copy_value(
                                                        ctx, BC_OPS, OP_OFF(self_pos), BC_LOC,
                                                        ctx->param_count * VALUE_SIZE
                                                );
                                                jit_emit_mov(asm, BC_A0, BC_TY);
                                                jit_emit_add_imm(
                                                        asm, BC_A1, BC_OPS, OP_OFF(self_pos)
                                                );
                                                jit_emit_load_imm(
                                                        asm, BC_A2, (iptr)target
                                                );
                                                jit_emit_load_imm(
                                                        asm, BC_CALL,
                                                        (iptr)ty_inline_guard_member
                                                );
                                                bc_emit_runtime_call(ctx, BC_CALL);
                                                jit_emit_cbz(asm, BC_RET, inline_slow);

                                                bool emitted = bc_emit_inline_plan(
                                                        ctx, &plan, TY_INLINE_METHOD,
                                                        base, self_pos, scratch,
                                                        ctx->self_class, inline_slow
                                                );
                                                ASSERT(emitted);
                                                (void)emitted;
                                                jit_emit_jump(asm, inline_done);
                                                jit_emit_label(asm, inline_slow);
                                                jit_emit_mov(asm, BC_A0, BC_TY);
                                                jit_emit_add_imm(
                                                        asm, BC_A1, BC_OPS, result_off
                                                );
                                                jit_emit_load_imm(asm, BC_A2, 0);
                                                jit_emit_load_imm(asm, BC_A3, z);
                                                jit_emit_load_imm(asm, BC_A4, n);
                                                jit_emit_load_imm(
                                                        asm, BC_CALL,
                                                        (iptr)jit_rt_call_method
                                                );
                                                bc_emit_runtime_call(ctx, BC_CALL);
                                        }
                                }
                        }

                        if (inline_done < 0) {
                                if (builtin_method != NULL) {
                                        jit_emit_mov(asm, BC_A0, BC_TY);
                                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                        jit_emit_load_imm(asm, BC_A2, 0);
                                        jit_emit_load_imm(asm, BC_A3, (iptr)builtin_method);
                                        jit_emit_load_imm(asm, BC_A4, PACK32(builtin_vtype, z));
                                        jit_emit_load_imm(asm, BC_A5, n);
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_builtin_method);
                                        bc_emit_runtime_call(ctx, BC_CALL);
                                        DBG("CALL_METHOD (builtin fast path for %s)", M_NAME(z));
                                } else if (baked_method != NULL) {
                                        jit_emit_mov(asm, BC_A0, BC_TY);
                                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                        jit_emit_load_imm(asm, BC_A2, 0);
                                        jit_emit_load_imm(asm, BC_A3, (iptr)baked_method);
                                        jit_emit_load_imm(asm, BC_A4, PACK32(ctx->self_class->i, z));
                                        jit_emit_load_imm(asm, BC_A5, n);
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_self_method_guarded);
                                        bc_emit_runtime_call(ctx, BC_CALL);
                                } else {
                                        jit_emit_mov(asm, BC_A0, BC_TY);
                                        jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                        jit_emit_load_imm(asm, BC_A2, 0);
                                        jit_emit_load_imm(asm, BC_A3, z);
                                        jit_emit_load_imm(asm, BC_A4, n);
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_method);
                                        bc_emit_runtime_call(ctx, BC_CALL);
                                }
                        }

                        if (inline_done >= 0) {
                                jit_emit_label(asm, inline_done);
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
                        char const *kw_ip = (char const *)ip;
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (n == -1) {
                                BAIL("CALL_GLOBAL with spread not supported");
                        }

                        if (nkw > 0) {
                                ctx->sp -= n + nkw;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp + n + nkw));
                                jit_emit_load_imm(asm, BC_A2, gi);
                                jit_emit_load_imm(asm, BC_A3, n);
                                jit_emit_load_imm(asm, BC_A4, nkw);
                                jit_emit_load_imm(asm, BC_A5, (iptr)kw_ip);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_global_kw);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                ctx->sp++;
                                if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                                break;
                        }

                        DBG("CALL_GLOBAL(%s, argc=%d)", VSC(vm_global(ty, gi)), n);

                        ctx->sp -= n;

                        // Sync the Ty stack count
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp + n);

                        // If the global is a const builtin function, emit a direct call
                        if (SymbolIsConst(globals[gi]) && V_TYPE(*v_(Globals, gi)) == VALUE_BUILTIN_FUNCTION) {
                                BuiltinFunction *fn = V_BUILTIN_FUNCTION(*v_(Globals, gi));
                                int result_off = OP_OFF(ctx->sp);
                                char const *builtin_name = compiler_global_sym(ty, gi)->identifier;
                                bool direct_max = n == 2 && strcmp(builtin_name, "max") == 0;
                                int direct_math = n == 1 && strcmp(builtin_name, "sin") == 0 ? 1
                                                : n == 1 && strcmp(builtin_name, "cos") == 0 ? 2 : 0;
                                bool direct_numeric = direct_max || direct_math;
                                int lbl_builtin_generic = direct_numeric ? bc_next_label(ctx) : -1;
                                int lbl_builtin_done = direct_numeric ? bc_next_label(ctx) : -1;
                                if (direct_max) {
                                        jit_emit_add_imm(asm, BC_A0, BC_OPS, result_off);
                                        jit_emit_mov(asm, BC_A1, BC_A0);
                                        jit_emit_add_imm(asm, BC_A2, BC_OPS, result_off + VALUE_SIZE);
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_double_max);
                                        bc_emit_runtime_call(ctx, BC_CALL);
                                        jit_emit_cbz(asm, BC_RET, lbl_builtin_generic);
                                        jit_emit_jump(asm, lbl_builtin_done);
                                        jit_emit_label(asm, lbl_builtin_generic);
                                } else if (direct_math) {
                                        jit_emit_add_imm(asm, BC_A0, BC_OPS, result_off);
                                        jit_emit_mov(asm, BC_A1, BC_A0);
                                        jit_emit_load_imm(asm, BC_A2, direct_math);
                                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_double_math);
                                        bc_emit_runtime_call(ctx, BC_CALL);
                                        jit_emit_cbz(asm, BC_RET, lbl_builtin_generic);
                                        jit_emit_jump(asm, lbl_builtin_done);
                                        jit_emit_label(asm, lbl_builtin_generic);
                                }
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, result_off);
                                jit_emit_load_imm(asm, BC_A2, (iptr)fn);
                                jit_emit_load_imm(asm, BC_A3, n);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_builtin_function);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                if (direct_numeric) jit_emit_label(asm, lbl_builtin_done);

                                DBG("CALL_GLOBAL(%s) [direct builtin]", VSC(vm_global(ty, gi)));

                                ctx->sp++;
                                if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                                break;
                        }

                        Value *global = v_(Globals, gi);
                        int inline_done = bc_emit_inline_global(ctx, global, gi, n);
                        int lbl_cg_slow = bc_next_label(ctx);
                        int lbl_cg_done = bc_next_label(ctx);
                        JitFn *linked = NULL;
                        if (inline_done < 0 && jit_linkable_global(global, n)) {
                                linked = try_jit(ty, global);
                        }

                        if (linked != NULL) {
                                int lbl_link_miss = bc_next_label(ctx);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_load_imm(asm, BC_A1, gi);
                                jit_emit_load_imm(asm, BC_A2, n);
                                jit_emit_load_imm(asm, BC_A3, (iptr)linked);
                                jit_emit_load_imm(
                                        asm, BC_CALL,
                                        (iptr)jit_rt_linked_global_call
                                );
                                bc_emit_runtime_call(ctx, BC_CALL);
                                jit_emit_cbz(asm, BC_RET, lbl_link_miss);
                                jit_emit_cmp_ri(asm, BC_RET, 2);
                                jit_emit_branch_ne(asm, lbl_cg_done);
                                jit_emit_reload_stack(asm, ctx->bound);
                                jit_emit_jump(asm, lbl_cg_done);
                                jit_emit_label(asm, lbl_link_miss);
                        }

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_A1, gi);
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_fast_global_call);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_cbz(asm, BC_RET, lbl_cg_slow);
                        jit_emit_cmp_ri(asm, BC_RET, 2);
                        jit_emit_branch_ne(asm, lbl_cg_done);
                        jit_emit_reload_stack(asm, ctx->bound);
                        jit_emit_jump(asm, lbl_cg_done);

                        DBG("CALL_GLOBAL[%d](%s) [fast trampoline]", gi, VSC(vm_global(ty, gi)));

                        // Slow fallback: load global + call trampoline
                        jit_emit_label(asm, lbl_cg_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_A1, gi);
                        jit_emit_load_imm(asm, BC_S0, (iptr)vm_global);
                        bc_emit_runtime_call(ctx, BC_S0);
                        // x0 now has Value* to the global
                        jit_emit_mov(asm, BC_A2, BC_RET);  // fn ptr (was in x0)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A3, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_call_trampoline);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // Old trampoline may also signal JIT_CALL
                        jit_emit_cbz(asm, BC_RET, lbl_cg_done);

                        int cg_site_idx = ctx->call_site_count++;
                        int cg_resume_lbl = bc_next_label(ctx);
                        ctx->resume_labels[cg_site_idx] = cg_resume_lbl;

                        bc_emit_trampoline_signal(ctx, JIT_CALL, cg_site_idx + 1);

                        jit_emit_label(asm, cg_resume_lbl);
                        bc_raw_reset(ctx);
                        jit_emit_label(asm, lbl_cg_done);
                        if (inline_done >= 0) {
                                jit_emit_label(asm, inline_done);
                        }

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;

                        DBG("CALL_GLOBAL(%s)", VSC(vm_global(ty, gi)));
                        break;
                }

                CASE(YIELD) {
                        int site_idx = ctx->call_site_count++;
                        int resume_lbl = bc_next_label(ctx);
                        ctx->resume_labels[site_idx] = resume_lbl;
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);
                        bc_emit_trampoline_signal(ctx, JIT_YIELD, site_idx + 1);
                        jit_emit_label(asm, resume_lbl);
                        bc_raw_reset(ctx);
                        break;
                }

                CASE(YIELD_SOME) {
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_yield_some);
                        bc_emit_reentrant_call(ctx, BC_CALL);
                        jit_emit_reload_stack(asm, ctx->bound);
                        bc_raw_reset(ctx);
                        break;
                }

                CASE(YIELD_NONE) {
                        int site_idx = ctx->call_site_count++;
                        int resume_lbl = bc_next_label(ctx);
                        ctx->resume_labels[site_idx] = resume_lbl;
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);
                        bc_emit_trampoline_signal(ctx, JIT_YIELD_NONE, site_idx + 1);
                        jit_emit_label(asm, resume_lbl);
                        bc_raw_reset(ctx);
                        ctx->sp++;
                        break;
                }

                CASE(TAIL_CALL) {
                        if (ctx->sp < ctx->param_count) BAIL("TAIL_CALL operand underflow");
                        int first = ctx->sp - ctx->param_count;
                        for (int q = ctx->param_count - 1; q >= 0; --q)
                                bc_copy_value(ctx, BC_LOC, q * VALUE_SIZE, BC_OPS, OP_OFF(first + q));
                        /* A backward edge is a fresh basic-block entry.  Do not
                         * leak scratch values from argument copies into fused
                         * entry guards. */
                        jit_emit_load_imm(asm, BC_S0, 0);
                        if (ctx->bound > ctx->param_count) {
                                jit_emit_load_imm(asm, BC_S0, (i64)NANBOX_VALUE_NULL);
                                for (int q = ctx->param_count; q < ctx->bound; ++q)
                                        jit_emit_str64(asm, BC_S0, BC_LOC, q * VALUE_SIZE);
                        }
                        ctx->sp = 0;
                        bc_raw_reset(ctx);
                        jit_emit_jump(asm, bc_label_for(ctx, 0));
                        ctx->dead = true;
                        break;
                }

                CASE(RETURN)
                CASE(RETURN_PRESERVE_CTX) {
                        // Result stays on top of the interpreter stack
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);
                        // Jump to shared epilogue
                        int lbl_ret = bc_label_for(ctx, -1);
                        jit_emit_jump(asm, lbl_ret);
                        ctx->dead = true;
                        break;
                }

                CASE(RETURN_IF_NOT_NONE) {
                        int top_off = OP_OFF(ctx->sp - 1);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, top_off);
                        jit_emit_cmp_ri(asm, BC_S0, NANBOX_VALUE_UNDEFINED);
                        int lbl_skip = bc_next_label(ctx);
                        jit_emit_branch_eq(asm, lbl_skip);
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);
                        jit_emit_jump(asm, bc_label_for(ctx, -1));
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
                        // Load global[n].  Large byte offsets exceed ARM64's
                        // scaled load-immediate range and need an address add.
                        jit_emit_load_imm(asm, BC_S2, (iptr)&Globals);
                        jit_emit_ldr64(asm, BC_S3, BC_S2, OFF_VEC_DATA);
                        if ((usize)n * sizeof (Value) <= 4095 * sizeof (u64)) {
                                bc_push_from(ctx, BC_S3, n * sizeof (Value));
                        } else {
                                jit_emit_load_imm(asm, BC_S2, (iptr)(n * sizeof (Value)));
                                jit_emit_add(asm, BC_S3, BC_S3, BC_S2);
                                bc_push_from(ctx, BC_S3, 0);
                        }
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
                        jit_emit_ldr64(asm, BC_S0, BC_S3, n * sizeof (Value));
                        jit_emit_cmp_ri(asm, BC_S0, NANBOX_VALUE_UNDEFINED);
                        jit_emit_branch_ne(asm, lbl_fast);
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_tls0);
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        Value value = value_box(ctx->ty, (ValuePayload){
                                .type=VALUE_TYPE, .ptr=(void *)p
                        });
                        gc_immortalize(ctx->ty, &value);
                        bc_push_bits(ctx, value.bits.as_int64, NULL);
                        break;
                }

                CASE(REGEX) {
                        uptr p;
                        BC_READ(p);
                        Value value = value_box(ctx->ty, (ValuePayload){
                                .type=VALUE_REGEX, .regex=(Regex const *)p
                        });
                        gc_immortalize(ctx->ty, &value);
                        bc_push_bits(ctx, value.bits.as_int64, NULL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
                        ctx->sp = saved + 1;
                        DBG("ARRAY literal");
                        break;
                }

                CASE(ARRAY0) {
                        // Empty array
                        int off = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_array0);
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
                        ctx->sp = saved;
                        break;
                }

                CASE(DUP2_SWAP) {
                        if (bc_try_range_guard(ctx, code, end, &ip, locals, off)) {
                                break;
                        }
                        // Before: ..., A, B (sp=N)
                        // After:  ..., A, B, B, A (sp=N+2)
                        // Copy B (at sp-1) to sp
                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_OPS, OP_OFF(ctx->sp - 1));
                        ctx->op_types[ctx->sp] = ctx->op_types[ctx->sp - 1];
                        ctx->sp++;
                        // Copy A (now at sp-3) to sp
                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_OPS, OP_OFF(ctx->sp - 3));
                        ctx->op_types[ctx->sp] = ctx->op_types[ctx->sp - 3];
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
                        if (VALUE_SIZE == 8) BAIL("TARGET_REF requires nanbox runtime lowering");
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
                                bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        DBG("CHECK_MATCH");
                        break;
                }

                CASE(ASSIGN_SUBSCRIPT) {
                        u8 n;
                        BC_READ(n);
                        if (n != 1) BAIL("multi-index assignment not supported");
                        int val = OP_OFF(ctx->sp - 3);
                        int con = OP_OFF(ctx->sp - 2);
                        int idx = OP_OFF(ctx->sp - 1);
                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, con);
                        jit_emit_decode_direct_array(asm, BC_S1, BC_S0, lbl_slow);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, idx);
                        jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
                        bc_decode_int32(ctx, BC_S0, BC_S0);
                        jit_emit_ldr64(asm, BC_S2, BC_S1, offsetof(Array, count));
                        jit_emit_cmp_ri(asm, BC_S0, 0);
                        int lbl_nonneg = bc_next_label(ctx);
                        jit_emit_branch_ge(asm, lbl_nonneg);
                        jit_emit_add(asm, BC_S0, BC_S0, BC_S2);
                        jit_emit_label(asm, lbl_nonneg);
                        jit_emit_cmp_ri(asm, BC_S0, 0);
                        jit_emit_branch_lt(asm, lbl_slow);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S2);
                        jit_emit_branch_ge(asm, lbl_slow);
                        jit_emit_ldr64(asm, BC_S1, BC_S1, offsetof(Array, items));
                        jit_emit_ldr64(asm, BC_S2, BC_OPS, val);
                        jit_emit_str64_index8(asm, BC_S2, BC_S1, BC_S0);
                        jit_emit_jump(asm, lbl_done);
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_array_set_semantic);
                        bc_emit_reentrant_call(ctx, BC_CALL);
                        jit_emit_label(asm, lbl_done);
                        ctx->sp -= 2;
                        break;
                }

                CASE(QUESTION) {
                        BAIL("QUESTION unsupported");
                        return false;
                }

                CASE(TAG) {
                        int tag;
                        BC_READ(tag);
                        Value value = value_direct_tag(tag);
                        bc_push_bits(ctx, value.bits.as_int64, NULL);
                        break;
                }

                CASE(CLASS) {
                        int cls;
                        BC_READ(cls);
                        int off = OP_OFF(ctx->sp);
                        Value value = value_direct_class(cls);
                        jit_emit_load_imm(asm, BC_S0, (i64)value.bits.as_int64);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off);
                        ctx->op_known_class[ctx->sp] = cls;
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(SUBSCRIPT) {
                        int con = OP_OFF(ctx->sp - 2);
                        int idx = OP_OFF(ctx->sp - 1);
                        int lbl_slow = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, con);
                        jit_emit_decode_direct_array(asm, BC_S1, BC_S0, lbl_slow);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, idx);
                        jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
                        bc_decode_int32(ctx, BC_S0, BC_S0);
                        jit_emit_ldr64(asm, BC_S2, BC_S1, offsetof(Array, count));
                        jit_emit_cmp_ri(asm, BC_S0, 0);
                        int lbl_nonneg = bc_next_label(ctx);
                        jit_emit_branch_ge(asm, lbl_nonneg);
                        jit_emit_add(asm, BC_S0, BC_S0, BC_S2);
                        jit_emit_label(asm, lbl_nonneg);
                        jit_emit_cmp_ri(asm, BC_S0, 0);
                        jit_emit_branch_lt(asm, lbl_slow);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S2);
                        jit_emit_branch_ge(asm, lbl_slow);
                        jit_emit_ldr64(asm, BC_S1, BC_S1, offsetof(Array, items));
                        jit_emit_ldr64_index8(asm, BC_S0, BC_S1, BC_S0);
                        jit_emit_str64(asm, BC_S0, BC_OPS, con);
                        jit_emit_jump(asm, lbl_done);
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, con);
                        jit_emit_mov(asm, BC_A2, BC_A1);
                        jit_emit_add_imm(asm, BC_A3, BC_OPS, idx);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_array_get);
                        bc_emit_reentrant_call(ctx, BC_CALL);
                        jit_emit_label(asm, lbl_done);
                        ctx->sp--;
                        break;
                }

                CASE(NONE_IF_NIL) {
                        // If TOS is nil, replace with NONE
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_not_nil = bc_next_label(ctx);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_S1, NANBOX_VALUE_NULL);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
                        jit_emit_branch_ne(asm, lbl_not_nil);
                        // Is nil: set type to VALUE_NONE
                        jit_emit_load_imm(asm, BC_S0, NANBOX_VALUE_UNDEFINED);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off);
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
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_S1, NANBOX_VALUE_NULL);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
                        jit_emit_branch_ne(asm, lbl_not_nil);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_bad_match);
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
                        // vm_throw never returns
                        ctx->dead = true;
                        break;
                }

                CASE(TRY) {
                        int catch_off, finally_off, end_off;
                        BC_READ(catch_off);
                        int catch_target = (int)(ip - code) + catch_off;

                        BC_READ(finally_off);
                        int finally_target = (finally_off == -1) ? -1 : (int)(ip - code) + finally_off;

                        BC_READ(end_off);
                        int end_target = (end_off == -1) ? -1 : (int)(ip - code) + end_off;

                        if (ctx->try_depth >= MAX_JIT_TRY) {
                                BAIL("too many nested try blocks");
                        }

                        // Record try block info
                        JitTryInfo *ti = &ctx->try_info[ctx->try_depth++];
                        ti->sp = ctx->sp;
                        ti->end_addr = (end_target >= 0) ? (code + end_target) : NULL;
                        ti->finally_label = (finally_target >= 0) ? bc_label_for(ctx, finally_target) : -1;
                        ti->end_label = (end_target >= 0) ? bc_label_for(ctx, end_target) : -1;
                        ti->n_finally_resumes = 0;

                        int catch_label = bc_label_for(ctx, catch_target);

                        // Compute bytecode addresses for catch/finally/end
                        char *catch_addr = (char *)(code + catch_target);
                        char *finally_addr = (finally_target >= 0) ? (char *)(code + finally_target) : NULL;
                        char *end_addr_val = (end_target >= 0) ? (char *)(code + end_target) : NULL;

                        // Sync stack so PushTry saves the correct state
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);

                        // Call jit_rt_push_try(ty, ops_top, catch, finally, end) -> returns jmp_buf*
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_A2, (iptr)catch_addr);
                        jit_emit_load_imm(asm, BC_A3, (iptr)finally_addr);
                        jit_emit_load_imm(asm, BC_A4, (iptr)end_addr_val);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_push_try);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // Call _setjmp(jmp_buf) from JIT code frame
                        // BC_RET has the jmp_buf pointer from jit_rt_push_try
                        jit_emit_mov(asm, BC_A0, BC_RET);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)_setjmp);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // If _setjmp returned non-zero: exception was caught
                        // DoThrow has restored VM state and pushed [SENTINEL, exception]
                        // Reload stack pointers (may have been reallocated) and jump to catch
                        int lbl_exc = bc_next_label(ctx);
                        jit_emit_cbnz(asm, BC_RET, lbl_exc);

                        // Normal path: _setjmp returned 0, continue with try body
                        // Jump over exception setup code
                        int lbl_try_body = bc_next_label(ctx);
                        jit_emit_jump(asm, lbl_try_body);

                        // Exception path: reload stack and jump to catch label
                        jit_emit_label(asm, lbl_exc);
                        jit_emit_reload_stack(asm, ctx->bound);

                        // Set catch label sp: at catch, stack = try_sp + 2 (SENTINEL + exception)
                        bc_set_label_sp(ctx, catch_target, ti->sp + 2);
                        jit_emit_jump(asm, catch_label);

                        // Try body starts here
                        jit_emit_label(asm, lbl_try_body);

                        break;
                }

                CASE(CATCH) {
                        // PopThrowCtx + set state to TRY_FINALLY
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_catch);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        break;
                }

                CASE(RETHROW) {
                        // Set state to TRY_THROW, end to NULL, jump to finally
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_rethrow_setup);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // Jump to finally code for current try block
                        if (ctx->try_depth <= 0) {
                                BAIL("RETHROW outside try block");
                        }
                        JitTryInfo *ti = &ctx->try_info[ctx->try_depth - 1];
                        if (ti->finally_label >= 0) {
                                jit_emit_jump(asm, ti->finally_label);
                        }
                        ctx->dead = true;
                        break;
                }

                CASE(FINALLY) {
                        // FINALLY instruction (for early return/break inside try body):
                        // Set state to TRY_FINALLY, save resume address, jump to finally code
                        if (ctx->try_depth <= 0) {
                                BAIL("FINALLY outside try block");
                        }
                        JitTryInfo *ti = &ctx->try_info[ctx->try_depth - 1];

                        // The bytecode address right after this FINALLY instruction
                        // is the resume point after finally code runs
                        char const *resume_addr = (char *)(code + (int)(ip - code));

                        // Create a label for the resume point
                        int resume_off = (int)(ip - code);
                        int resume_label = bc_label_for(ctx, resume_off);
                        bc_set_label_sp(ctx, resume_off, ctx->sp);

                        // Register this resume in the try info
                        if (ti->n_finally_resumes < 8) {
                                ti->finally_resumes[ti->n_finally_resumes].addr = resume_addr;
                                ti->finally_resumes[ti->n_finally_resumes].label = resume_label;
                                ti->n_finally_resumes++;
                        }

                        // Call jit_rt_finally_enter(ty, resume_addr)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_A1, (iptr)resume_addr);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_finally_enter);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // Jump to finally code
                        if (ti->finally_label >= 0) {
                                jit_emit_jump(asm, ti->finally_label);
                        }

                        ctx->dead = true;
                        break;
                }

                CASE(END_TRY) {
                        if (ctx->try_depth <= 0) {
                                BAIL("END_TRY outside try block");
                        }
                        JitTryInfo *ti = &ctx->try_info[ctx->try_depth - 1];

                        // Call jit_rt_end_try(ty) -> returns _try->end
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_end_try);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // If end is NULL: re-throw (doesn't return)
                        int lbl_not_null = bc_next_label(ctx);
                        jit_emit_cbnz(asm, BC_RET, lbl_not_null);

                        // Re-throw path
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_end_try_rethrow);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        // Doesn't return (longjmps to outer handler)

                        jit_emit_label(asm, lbl_not_null);

                        // Dispatch based on _try->end value
                        // Check if it's the normal end address
                        if (ti->end_label >= 0 && ti->end_addr != NULL) {
                                jit_emit_load_imm(asm, BC_S0, (iptr)ti->end_addr);
                                jit_emit_cmp_rr(asm, BC_RET, BC_S0);
                                jit_emit_branch_eq(asm, ti->end_label);
                        }

                        // Check FINALLY resume points
                        for (int q = 0; q < ti->n_finally_resumes; ++q) {
                                jit_emit_load_imm(asm, BC_S0, (iptr)ti->finally_resumes[q].addr);
                                jit_emit_cmp_rr(asm, BC_RET, BC_S0);
                                jit_emit_branch_eq(asm, ti->finally_resumes[q].label);
                        }

                        // Fallback: jump to end label if we have one
                        if (ti->end_label >= 0) {
                                jit_emit_jump(asm, ti->end_label);
                        }

                        ctx->try_depth--;
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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_HIGH16_TAG);
                        jit_emit_and(asm, BC_S1, BC_S0, BC_S2);
                        jit_emit_load_imm(asm, BC_S2, (i64)NANBOX_MIN_NUMBER);
                        jit_emit_cmp_rr(asm, BC_S1, BC_S2);
                        jit_emit_branch_ne(asm, lbl_slow);
                        bc_decode_int32(ctx, BC_S0, BC_S0);
                        jit_emit_add_imm(asm, BC_S0, BC_S0, 1);
                        bc_encode_int32(ctx, BC_S0, BC_S0);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off);
                        jit_emit_jump(asm, lbl_done);
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_inc);
                        bc_emit_reentrant_call(ctx, BC_CALL);
                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(DEC) {
                        int off = OP_OFF(ctx->sp - 1);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_dec);
                        bc_emit_reentrant_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        ctx->op_types[ctx->sp - 1] = STRING_TYPE;
                        break;
                }

                CASE(REAL) {
                        double x;
                        BC_READ(x);
                        Value v = value_real(x);
                        bc_push_bits(ctx, v.bits.as_int64, TYPE_FLOAT);
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
                        if (VALUE_SIZE == 8) BAIL("GET_TAG requires nanbox runtime lowering");
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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        if (!wrapped) {
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, off);
                                jit_emit_decode_direct_tag(asm, BC_S0, BC_S0, fail_lbl);
                        } else {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                                jit_emit_load_imm(asm, BC_A2, wrapped);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_match_tag_id);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                jit_emit_mov(asm, BC_S0, BC_RET);
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
                        char const *name = intern_entry(&xD.b_ops, n)->name;
                        if (getenv("TY_JIT_NO_NUMERIC_POW") == NULL
                            && strcmp(name, "**") == 0) {
                                int left_off = OP_OFF(ctx->sp - 2);
                                int right_off = OP_OFF(ctx->sp - 1);
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(
                                        asm, BC_A1, BC_OPS, left_off
                                );
                                jit_emit_add_imm(
                                        asm, BC_A2, BC_OPS, right_off
                                );
                                jit_emit_load_imm(
                                        asm, BC_CALL,
                                        (iptr)jit_rt_numeric_pow
                                );
                                bc_emit_runtime_call(ctx, BC_CALL);
                                jit_emit_cmp_ri32(asm, BC_RET, 0);
                                jit_emit_branch_eq(asm, lbl_slow);
                                jit_emit_jump(asm, lbl_done);
                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(
                                        asm, BC_A1, BC_OPS,
                                        OP_OFF(ctx->sp)
                                );
                                jit_emit_load_imm(asm, BC_A2, n);
                                jit_emit_load_imm(
                                        asm, BC_CALL,
                                        (iptr)jit_rt_binary_op
                                );
                                bc_emit_reentrant_call(ctx, BC_CALL);
                                jit_emit_label(asm, lbl_done);
                        } else {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(
                                        asm, BC_A1, BC_OPS,
                                        OP_OFF(ctx->sp)
                                );
                                jit_emit_load_imm(asm, BC_A2, n);
                                jit_emit_load_imm(
                                        asm, BC_CALL,
                                        (iptr)jit_rt_binary_op
                                );
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        }
                        ctx->sp--;
                        ctx->op_types[ctx->sp - 1] = NULL;
                        break;
                }

                CASE(JUMP_WTF) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) BAIL("invalid JUMP_WTF target");

                        int tos_off = OP_OFF(ctx->sp - 1);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_S1, NANBOX_VALUE_NULL);
                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);

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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                                bc_emit_runtime_call(ctx, BC_CALL);
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
                                int lbl_slow_mut = bc_next_label(ctx), lbl_done_mut = bc_next_label(ctx);
                                jit_emit_ldr64(asm, BC_S3, BC_ENV, n * 8);
                                jit_emit_ldr64(asm, BC_S0, BC_S3, 0);
                                jit_emit_ldr64(asm, BC_S1, BC_OPS, addend_off);
                                jit_emit_branch_not_int32(asm, BC_S0, lbl_slow_mut);
                                jit_emit_branch_not_int32(asm, BC_S1, lbl_slow_mut);
                                bc_decode_int32(ctx, BC_S0, BC_S0);
                                bc_decode_int32(ctx, BC_S1, BC_S1);
                                if (mut_op == INSTR_MUT_ADD)
                                        jit_emit_add32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow_mut);
                                else
                                        jit_emit_sub32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow_mut);
                                bc_encode_int32(ctx, BC_S0, BC_S0);
                                jit_emit_str64(asm, BC_S0, BC_S3, 0);
                                jit_emit_str64(asm, BC_S0, BC_OPS, addend_off);
                                jit_emit_jump(asm, lbl_done_mut);
                                jit_emit_label(asm, lbl_slow_mut);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_mov(asm, BC_A1, BC_S3);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, addend_off);
                                jit_emit_mov(asm, BC_A3, BC_A2);
                                jit_emit_load_imm(asm, BC_CALL, mut_op == INSTR_MUT_ADD
                                        ? (iptr)jit_rt_mut_add : (iptr)jit_rt_mut_sub);
                                bc_emit_runtime_call(ctx, BC_CALL);
                                jit_emit_label(asm, lbl_done_mut);
                                // sp unchanged
                        } else {
                                // Load env[n] pointer => BC_S2
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_ldr64(asm, BC_A1, BC_ENV, n * 8);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_push_target);
                                bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);

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

                        jit_emit_add_imm(asm, BC_A0, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_A1, type_val);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_is_type);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_ne(asm, lbl_target);
                        break;
                }

                CASE(ENSURE_LEN_TUPLE) {
                        int jump_off; BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid ENSURE_LEN_TUPLE target");
                        int expected_count; BC_READ(expected_count);
                        int tos_off = OP_OFF(ctx->sp - 1);
                        jit_emit_add_imm(asm, BC_A0, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_A1, expected_count);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_ensure_len_tuple);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);
                        break;
                }

                CASE(TRY_ASSIGN_NON_NIL) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid TRY_ASSIGN_NON_NIL target");
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_assign_non_nil);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_cbz(asm, BC_RET, fail_lbl);
                        break;
                }

                CASE(TAG_PUSH) {
                        int tag;
                        BC_READ(tag);

                        int val_off = OP_OFF(ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, val_off);
                        jit_emit_load_imm(asm, BC_A2, tag);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_tag_push);
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        int done_lbl = bc_next_label(ctx);
                        int slow_lbl = bc_next_label(ctx);

                        if (tag == TAG_SOME) {
                                u32 expected = ((u32)0x0005 << 16) | some_tag_chain(ty);
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, val_off);
                                jit_emit_load_imm(asm, BC_S2, 32);
                                jit_emit_shr(asm, BC_S1, BC_S0, BC_S2);
                                jit_emit_load_imm(asm, BC_S2, expected);
                                jit_emit_cmp_rr(asm, BC_S1, BC_S2);
                                jit_emit_branch_ne(asm, slow_lbl);
                                bc_encode_int32(ctx, BC_S0, BC_S0);
                                jit_emit_str64(asm, BC_S0, BC_OPS, val_off);
                                jit_emit_load_imm(asm, BC_RET, 1);
                                jit_emit_jump(asm, done_lbl);
                        } else {
                                jit_emit_jump(asm, slow_lbl);
                        }

                        jit_emit_label(asm, slow_lbl);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, val_off);
                        jit_emit_load_imm(asm, BC_A2, tag);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_tag_pop);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_label(asm, done_lbl);

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
                        bc_emit_runtime_call(ctx, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(PUSH_TUPLE_ELEM) {
                        i32 idx;
                        BC_READ(idx);
                        int lbl_fail = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);
                        int top_off = OP_OFF(ctx->sp - 1);
                        int dst_off = OP_OFF(ctx->sp);
                        jit_emit_add_imm(asm, BC_A0, BC_OPS, top_off);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, dst_off);
                        jit_emit_load_imm(asm, BC_A2, idx);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_index_tuple);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        jit_emit_branch_eq(asm, lbl_fail);
                        jit_emit_jump(asm, lbl_done);
                        jit_emit_label(asm, lbl_fail);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, top_off);
                        jit_emit_load_imm(asm, BC_A2, (iptr)(code + off));
                        jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_fail);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_label(asm, lbl_done);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                                CASE(PUSH_ARRAY_ELEM) {
                        if (VALUE_SIZE == 8) BAIL("PUSH_ARRAY_ELEM requires nanbox runtime lowering");
                        i32 idx;
                        u8 strict;
                        BC_READ(idx);
                        BC_READ(strict);
                        if (idx < 0) {
                                BAIL("PUSH_ARRAY_ELEM with negative index");
                        }
                        int top_off = OP_OFF(ctx->sp - 1);
                        int lbl_fail = bc_next_label(ctx);
                        int lbl_done = bc_next_label(ctx);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, top_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_ARRAY);
                        jit_emit_branch_ne(asm, lbl_fail);
                        jit_emit_ldr64(asm, BC_S3, BC_OPS, top_off + VAL_OFF_Z);
                        jit_emit_ldr64(asm, BC_S0, BC_S3, 8);
                        jit_emit_cmp_ri(asm, BC_S0, idx);
                        jit_emit_branch_le(asm, lbl_fail);
                        jit_emit_ldr64(asm, BC_S3, BC_S3, 0);
                        bc_push_from(ctx, BC_S3, idx * sizeof (Value));
                        jit_emit_jump(asm, lbl_done);
                        jit_emit_label(asm, lbl_fail);
                        if (strict) {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, top_off);
                                jit_emit_load_imm(asm, BC_A2, (iptr)(code + off));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)vm_jit_fail);
                                bc_emit_runtime_call(ctx, BC_CALL);
                        } else {
                                bc_push_nil(ctx);
                        }
                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(INDEX_TUPLE) {
                        int jump_off; BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid INDEX_TUPLE target");
                        int idx; BC_READ(idx);
                        int tos_off = OP_OFF(ctx->sp - 1);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        int dst_off = OP_OFF(ctx->sp);
                        jit_emit_add_imm(asm, BC_A0, BC_OPS, tos_off);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, dst_off);
                        jit_emit_load_imm(asm, BC_A2, idx);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_index_tuple);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_cmp_ri(asm, BC_RET, 0);
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
                        bc_emit_runtime_call(ctx, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(TRY_REGEX) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid TRY_REGEX target");

                        uptr re;
                        BC_READ(re);

                        int tos_off = OP_OFF(ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_A2, (iptr)re);
                        jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_regex);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(ASSIGN_REGEX_MATCHES) {
                        int n;
                        BC_READ(n);

                        int match_off = OP_OFF(ctx->sp - 1);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, match_off);
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_assign_regex_matches);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        ctx->sp--;
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
                        bc_emit_runtime_call(ctx, BC_CALL);
                        jit_emit_mov(asm, BC_A2, BC_RET);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_try_steal_tag);
                        bc_emit_runtime_call(ctx, BC_CALL);

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
                        bc_emit_runtime_call(ctx, BC_CALL);

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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);

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
                        bc_emit_runtime_call(ctx, BC_CALL);

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
                        bc_emit_runtime_call(ctx, BC_CALL);

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
                        if (VALUE_SIZE == 8) BAIL("ENSURE_LEN requires nanbox runtime lowering");
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

                CASE(ARRAY_REST) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid ARRAY_REST target");

                        int start, suffix;
                        BC_READ(start);
                        BC_READ(suffix);

                        int tos_off = OP_OFF(ctx->sp - 1);

                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);

                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_A2, start);
                        jit_emit_load_imm(asm, BC_A3, suffix);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_array_rest);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);
                        break;
                }

                CASE(TUPLE_REST) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid TUPLE_REST target");

                        int start;
                        BC_READ(start);

                        int tos_off = OP_OFF(ctx->sp - 1);

                        // Sync stack for poptarget
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);

                        // Call jit_rt_tuple_rest(ty, tos, start)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_A2, start);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_tuple_rest);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // If returned 0: not a tuple, jump to fail
                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);
                        break;
                }

                CASE(RECORD_REST) {
                        int jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        int fail_lbl = bc_find_label(ctx, target);
                        if (fail_lbl < 0) BAIL("invalid RECORD_REST target");

                        // Skip alignment padding, then grab pointer to excluded IDs list
                        ip = ALIGNED_FOR(i32, ip);
                        i32 const *excluded_ids = (i32 const *)ip;

                        // Advance ip past the -1 terminated list
                        while (*(i32 const *)ip != -1) ip += sizeof (i32);
                        ip += sizeof (i32);

                        int tos_off = OP_OFF(ctx->sp - 1);

                        // Sync stack for poptarget
                        jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);

                        // Call jit_rt_record_rest(ty, tos, excluded_ids)
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, tos_off);
                        jit_emit_load_imm(asm, BC_A2, (iptr)excluded_ids);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_record_rest);
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // If returned 0: not a record, jump to fail
                        jit_emit_cmp_ri(asm, BC_RET, 0);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, fail_lbl);
                        break;
                }

                CASE(CLEAR_RC) {
                        // ty->st->rc = 0;
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_str32(asm, BC_S0, BC_TY, (int)offsetof(co_state, rc));
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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);

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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);

                        // argc args consumed, 1 result produced
                        ctx->sp -= (argc - 1);
                        break;
                }

                CASE(MUT_ADD)
                CASE(MUT_SUB)
                CASE(MUT_MUL)
                CASE(MUT_DIV)
                CASE(MUT_MOD) {
                        int off = OP_OFF(ctx->sp - 1);
                        void *runtime = bc_mut_runtime(op);
                        if (ctx->tgt_kind == TGT_LOCAL
                            && (op == INSTR_MUT_ADD || op == INSTR_MUT_SUB || op == INSTR_MUT_MUL)) {
                                int local = ctx->tgt_index * VALUE_SIZE;
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);
                                jit_emit_ldr64(asm, BC_S0, BC_LOC, local);
                                jit_emit_ldr64(asm, BC_S1, BC_OPS, off);
                                jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
                                jit_emit_branch_not_int32(asm, BC_S1, lbl_slow);
                                bc_decode_int32(ctx, BC_S0, BC_S0);
                                bc_decode_int32(ctx, BC_S1, BC_S1);
                                if (op == INSTR_MUT_ADD) jit_emit_add32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
                                else if (op == INSTR_MUT_SUB) jit_emit_sub32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
                                else jit_emit_mul32_overflow(asm, BC_S0, BC_S0, BC_S1, lbl_slow);
                                bc_encode_int32(ctx, BC_S0, BC_S0);
                                jit_emit_str64(asm, BC_S0, BC_LOC, local);
                                jit_emit_str64(asm, BC_S0, BC_OPS, off);
                                jit_emit_jump(asm, lbl_done);
                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, local);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, off);
                                jit_emit_mov(asm, BC_A3, BC_A2);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)runtime);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_LOCAL) {
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, ctx->tgt_index * VALUE_SIZE);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, off);
                                jit_emit_mov(asm, BC_A3, BC_A2);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)runtime);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SUBSCRIPT
                                   && (op == INSTR_MUT_ADD || op == INSTR_MUT_SUB || op == INSTR_MUT_MUL)) {
                                int con = OP_OFF(ctx->tgt_obj_sp);
                                int idx = OP_OFF(ctx->tgt_index);
                                int lbl_slow = bc_next_label(ctx), lbl_done = bc_next_label(ctx);
                                jit_emit_ldr64(asm, BC_S1, BC_OPS, con);
                                jit_emit_decode_direct_array(asm, BC_S1, BC_S1, lbl_slow);
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, idx);
                                bc_decode_int32(ctx, BC_S0, BC_S0);
                                jit_emit_ldr64(asm, BC_S2, BC_S1, offsetof(Array, count));
                                jit_emit_cmp_ri(asm, BC_S0, 0);
                                int lbl_nonneg = bc_next_label(ctx);
                                jit_emit_branch_ge(asm, lbl_nonneg);
                                jit_emit_add(asm, BC_S0, BC_S0, BC_S2);
                                jit_emit_label(asm, lbl_nonneg);
                                jit_emit_cmp_ri(asm, BC_S0, 0);
                                jit_emit_branch_lt(asm, lbl_slow);
                                jit_emit_cmp_rr(asm, BC_S0, BC_S2);
                                jit_emit_branch_ge(asm, lbl_slow);
                                jit_emit_ldr64(asm, BC_S1, BC_S1, offsetof(Array, items));
                                jit_emit_ldr64_index8(asm, BC_S3, BC_S1, BC_S0); /* element */
                                jit_emit_ldr64(asm, BC_S2, BC_OPS, off); /* addend */
                                /* Guard both immediate int tags. */
                                jit_emit_branch_not_int32(asm, BC_S3, lbl_slow);
                                jit_emit_branch_not_int32(asm, BC_S2, lbl_slow);
                                bc_decode_int32(ctx, BC_S3, BC_S3);
                                bc_decode_int32(ctx, BC_S2, BC_S2);
                                if (op == INSTR_MUT_ADD) jit_emit_add32_overflow(asm, BC_S3, BC_S3, BC_S2, lbl_slow);
                                else if (op == INSTR_MUT_SUB) jit_emit_sub32_overflow(asm, BC_S3, BC_S3, BC_S2, lbl_slow);
                                else jit_emit_mul32_overflow(asm, BC_S3, BC_S3, BC_S2, lbl_slow);
                                bc_encode_int32(ctx, BC_S3, BC_S3);
                                jit_emit_str64_index8(asm, BC_S3, BC_S1, BC_S0);
                                jit_emit_str64(asm, BC_S3, BC_OPS, off);
                                jit_emit_jump(asm, lbl_done);
                                jit_emit_label(asm, lbl_slow);
                                void *subruntime = op == INSTR_MUT_ADD ? (void *)jit_rt_subscript_mut_add
                                        : op == INSTR_MUT_SUB ? (void *)jit_rt_subscript_mut_sub
                                        : (void *)jit_rt_subscript_mut_mul;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, con);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, idx);
                                jit_emit_load_imm(asm, BC_CALL, (iptr)subruntime);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_SUBSCRIPT) {
                                void *subruntime = op == INSTR_MUT_ADD ? (void *)jit_rt_subscript_mut_add
                                        : op == INSTR_MUT_SUB ? (void *)jit_rt_subscript_mut_sub
                                        : op == INSTR_MUT_MUL ? (void *)jit_rt_subscript_mut_mul
                                        : op == INSTR_MUT_DIV ? (void *)jit_rt_subscript_mut_div
                                        : (void *)jit_rt_subscript_mut_mod;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->tgt_obj_sp));
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->tgt_index));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)subruntime);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else BAIL("nanbox mutation target not supported");
                        ctx->tgt_kind = TGT_NONE;
                        break;
                }

                CASE(POST_INC) {
                        if (ctx->tgt_kind == TGT_NONE) {
                                BAIL("JIT: POST_INC without target");
                        }

                        if (ctx->tgt_kind == TGT_LOCAL) {
                                int local_off = ctx->tgt_index * VALUE_SIZE;
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                Type *t0 = locals[ctx->tgt_index]->type;
                                Class *class0 = expected_class_of(ctx->ty, t0);

                                if (VALUE_SIZE != 8 && class0 != NULL && class0->i == CLASS_INT) {
                                        // Fast path: check target is VALUE_INTEGER
                                        jit_emit_ldrb(asm, BC_S0, BC_LOC, local_off + VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        // Push original value as result
                                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_LOC, local_off);

                                        // Mutate local: load, increment, and store back
                                        jit_emit_ldr64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);
                                        jit_emit_add_imm(asm, BC_S0, BC_S0, 1);
                                        jit_emit_str64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                // Slow path
                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, local_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_inc);
                                bc_emit_reentrant_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_CAPTURED) {
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                Type *t0 = locals[ctx->tgt_index]->type;
                                Class *class0 = expected_class_of(ctx->ty, t0);

                                jit_emit_ldr64(asm, BC_S2, BC_ENV, ctx->tgt_index * 8);

                                if (VALUE_SIZE != 8 && class0 != NULL && class0->i == CLASS_INT) {
                                        // Fast path: check target is VALUE_INTEGER
                                        jit_emit_ldrb(asm, BC_S0, BC_S2, VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        // Push original value as result
                                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_S2, 0);

                                        // Mutate local: load, increment, and store back
                                        jit_emit_ldr64(asm, BC_S0, BC_S2, VAL_OFF_Z);
                                        jit_emit_add_imm(asm, BC_S0, BC_S0, 1);
                                        jit_emit_str64(asm, BC_S0, BC_S2, VAL_OFF_Z);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                // Slow path
                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_mov(asm, BC_A1, BC_S2);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_inc);
                                bc_emit_reentrant_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_MEMBER) {
                                int obj_off = OP_OFF(ctx->tgt_obj_sp);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_inc_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SELF_MEMBER) {
                                int self_off = ctx->param_count * VALUE_SIZE;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, self_off);
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_inc_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SUBSCRIPT) {
                                int container_off = OP_OFF(ctx->tgt_obj_sp);
                                int subscript_off = OP_OFF(ctx->tgt_index);

                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, container_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, subscript_off);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_inc_subscript);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else {
                                BAIL("JIT: POST_INC on unsupported target kind");
                        }

                        ctx->tgt_kind = TGT_NONE;
                        ctx->sp++;
                        break;
                }

                CASE(POST_DEC) {
                        if (ctx->tgt_kind == TGT_NONE) {
                                BAIL("JIT: POST_DEC without target");
                        }

                        if (ctx->tgt_kind == TGT_LOCAL) {
                                int local_off = ctx->tgt_index * VALUE_SIZE;
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                Type *t0 = locals[ctx->tgt_index]->type;
                                Class *class0 = expected_class_of(ctx->ty, t0);

                                if (VALUE_SIZE != 8 && class0 != NULL && class0->i == CLASS_INT) {
                                        jit_emit_ldr64(asm, BC_S0, BC_LOC, local_off);
                                        jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
                                        jit_emit_str64(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp));
                                        bc_decode_int32(ctx, BC_S0, BC_S0);
                                        jit_emit_load_imm(asm, BC_S1, INT32_MIN);
                                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
                                        jit_emit_branch_eq(asm, lbl_slow);
                                        jit_emit_load_imm(asm, BC_S1, 1);
                                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                                        bc_encode_int32(ctx, BC_S0, BC_S0);
                                        jit_emit_str64(asm, BC_S0, BC_LOC, local_off);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, local_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_dec);
                                bc_emit_reentrant_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_CAPTURED) {
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                Type *t0 = locals[ctx->tgt_index]->type;
                                Class *class0 = expected_class_of(ctx->ty, t0);

                                jit_emit_ldr64(asm, BC_S2, BC_ENV, ctx->tgt_index * 8);

                                if (VALUE_SIZE != 8 && class0 != NULL && class0->i == CLASS_INT) {
                                        jit_emit_ldr64(asm, BC_S0, BC_S2, 0);
                                        jit_emit_branch_not_int32(asm, BC_S0, lbl_slow);
                                        jit_emit_str64(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp));
                                        bc_decode_int32(ctx, BC_S0, BC_S0);
                                        jit_emit_load_imm(asm, BC_S1, INT32_MIN);
                                        jit_emit_cmp_rr(asm, BC_S0, BC_S1);
                                        jit_emit_branch_eq(asm, lbl_slow);
                                        jit_emit_load_imm(asm, BC_S1, 1);
                                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                                        bc_encode_int32(ctx, BC_S0, BC_S0);
                                        jit_emit_str64(asm, BC_S0, BC_S2, 0);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_mov(asm, BC_A1, BC_S2);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_dec);
                                bc_emit_reentrant_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_MEMBER) {
                                int obj_off = OP_OFF(ctx->tgt_obj_sp);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_dec_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SELF_MEMBER) {
                                int self_off = ctx->param_count * VALUE_SIZE;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, self_off);
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_dec_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SUBSCRIPT) {
                                int container_off = OP_OFF(ctx->tgt_obj_sp);
                                int subscript_off = OP_OFF(ctx->tgt_index);

                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, container_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, subscript_off);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_post_dec_subscript);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else {
                                BAIL("JIT: POST_DEC on unsupported target kind");
                        }

                        ctx->tgt_kind = TGT_NONE;
                        ctx->sp++;
                        break;
                }

                CASE(PRE_INC) {
                        if (ctx->tgt_kind == TGT_NONE) {
                                BAIL("JIT: PRE_INC without target");
                        }

                        if (ctx->tgt_kind == TGT_LOCAL) {
                                int local_off = ctx->tgt_index * VALUE_SIZE;
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                Type *t0 = locals[ctx->tgt_index]->type;
                                Class *class0 = expected_class_of(ctx->ty, t0);

                                if (VALUE_SIZE != 8 && class0 != NULL && class0->i == CLASS_INT) {
                                        jit_emit_ldrb(asm, BC_S0, BC_LOC, local_off + VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        jit_emit_ldr64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);
                                        jit_emit_add_imm(asm, BC_S0, BC_S0, 1);
                                        jit_emit_str64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);

                                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_LOC, local_off);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, local_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_inc);
                                bc_emit_reentrant_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_CAPTURED) {
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                Type *t0 = locals[ctx->tgt_index]->type;
                                Class *class0 = expected_class_of(ctx->ty, t0);

                                jit_emit_ldr64(asm, BC_S2, BC_ENV, ctx->tgt_index * 8);

                                if (VALUE_SIZE != 8 && class0 != NULL && class0->i == CLASS_INT) {
                                        jit_emit_ldrb(asm, BC_S0, BC_S2, VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        jit_emit_ldr64(asm, BC_S0, BC_S2, VAL_OFF_Z);
                                        jit_emit_add_imm(asm, BC_S0, BC_S0, 1);
                                        jit_emit_str64(asm, BC_S0, BC_S2, VAL_OFF_Z);

                                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_S2, 0);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_mov(asm, BC_A1, BC_S2);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_inc);
                                bc_emit_reentrant_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_MEMBER) {
                                int obj_off = OP_OFF(ctx->tgt_obj_sp);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_inc_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SELF_MEMBER) {
                                int self_off = ctx->param_count * VALUE_SIZE;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, self_off);
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_inc_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SUBSCRIPT) {
                                int container_off = OP_OFF(ctx->tgt_obj_sp);
                                int subscript_off = OP_OFF(ctx->tgt_index);

                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, container_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, subscript_off);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_inc_subscript);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else {
                                BAIL("JIT: PRE_INC on unsupported target kind");
                        }

                        ctx->tgt_kind = TGT_NONE;
                        ctx->sp++;
                        break;
                }

                CASE(PRE_DEC) {
                        if (ctx->tgt_kind == TGT_NONE) {
                                BAIL("JIT: PRE_DEC without target");
                        }

                        if (ctx->tgt_kind == TGT_LOCAL) {
                                int local_off = ctx->tgt_index * VALUE_SIZE;
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                Type *t0 = locals[ctx->tgt_index]->type;
                                Class *class0 = expected_class_of(ctx->ty, t0);

                                if (VALUE_SIZE != 8 && class0 != NULL && class0->i == CLASS_INT) {
                                        jit_emit_ldrb(asm, BC_S0, BC_LOC, local_off + VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        jit_emit_ldr64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);
                                        jit_emit_load_imm(asm, BC_S1, 1);
                                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                                        jit_emit_str64(asm, BC_S0, BC_LOC, local_off + VAL_OFF_Z);

                                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_LOC, local_off);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, local_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_dec);
                                bc_emit_reentrant_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_CAPTURED) {
                                int lbl_slow = bc_next_label(ctx);
                                int lbl_done = bc_next_label(ctx);

                                Type *t0 = locals[ctx->tgt_index]->type;
                                Class *class0 = expected_class_of(ctx->ty, t0);

                                jit_emit_ldr64(asm, BC_S2, BC_ENV, ctx->tgt_index * 8);

                                if (VALUE_SIZE != 8 && class0 != NULL && class0->i == CLASS_INT) {
                                        jit_emit_ldrb(asm, BC_S0, BC_S2, VAL_OFF_TYPE);
                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                                        jit_emit_branch_ne(asm, lbl_slow);

                                        jit_emit_ldr64(asm, BC_S0, BC_S2, VAL_OFF_Z);
                                        jit_emit_load_imm(asm, BC_S1, 1);
                                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                                        jit_emit_str64(asm, BC_S0, BC_S2, VAL_OFF_Z);

                                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_S2, 0);
                                        jit_emit_jump(asm, lbl_done);
                                }

                                jit_emit_label(asm, lbl_slow);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_mov(asm, BC_A1, BC_S2);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_dec);
                                bc_emit_reentrant_call(ctx, BC_CALL);

                                jit_emit_label(asm, lbl_done);
                        } else if (ctx->tgt_kind == TGT_MEMBER) {
                                int obj_off = OP_OFF(ctx->tgt_obj_sp);
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, obj_off);
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_dec_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SELF_MEMBER) {
                                int self_off = ctx->param_count * VALUE_SIZE;
                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_LOC, self_off);
                                jit_emit_load_imm(asm, BC_A2, ctx->tgt_index);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_dec_member);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else if (ctx->tgt_kind == TGT_SUBSCRIPT) {
                                int container_off = OP_OFF(ctx->tgt_obj_sp);
                                int subscript_off = OP_OFF(ctx->tgt_index);

                                jit_emit_mov(asm, BC_A0, BC_TY);
                                jit_emit_add_imm(asm, BC_A1, BC_OPS, container_off);
                                jit_emit_add_imm(asm, BC_A2, BC_OPS, subscript_off);
                                jit_emit_add_imm(asm, BC_A3, BC_OPS, OP_OFF(ctx->sp));
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_pre_dec_subscript);
                                bc_emit_reentrant_call(ctx, BC_CALL);
                        } else {
                                BAIL("JIT: PRE_DEC on unsupported target kind");
                        }

                        ctx->tgt_kind = TGT_NONE;
                        ctx->sp++;
                        break;
                }

                CASE(PUSH_INDEX) {
                        int n;
                        BC_READ(n);
                        int dst = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, dst);
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_push_index);
                        bc_emit_reentrant_call(ctx, BC_CALL);
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
                        bc_emit_runtime_call(ctx, BC_CALL);
                        break;
                }

                CASE(PATCH_ENV) {
                        int n;
                        BC_READ(n);
                        int top_off = OP_OFF(ctx->sp - 1);
                        jit_emit_mov(asm, BC_A0, BC_TY);
                        jit_emit_add_imm(asm, BC_A1, BC_OPS, top_off);
                        jit_emit_load_imm(asm, BC_A2, n);
                        jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_patch_env);
                        bc_emit_runtime_call(ctx, BC_CALL);
                        break;
                }

                CASE(FUNCTION)
                CASE(GENERATOR) {
                        // Save the current IP position (before alignment)
                        // The runtime helper will align and parse the function info
                        char const *fn_ip = ip;

                        int bound_caps;
                        BC_READ(bound_caps);

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
                        if (op == INSTR_GENERATOR) {
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_generator);
                        } else {
                                jit_emit_load_imm(asm, BC_CALL, (iptr)jit_rt_function);
                        }
                        bc_emit_reentrant_call(ctx, BC_CALL);

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

                switch (op) {
                case INSTR_SAVE_STACK_POS:
                case INSTR_DROP_STACK_POS:
                case INSTR_RESTORE_STACK_POS:
                case INSTR_POP_STACK_POS_POP:
                        break;
                default:
                        stack_base_valid = bc_preserves_stack_base(op);
                        break;
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

static void
bc_free_cfg(JitCtx *ctx)
{
        free(ctx->cfg_nodes);
        free(ctx->cfg_index);
        free(ctx->cfg_dirty);
        free(ctx->raw_scores);
        free(ctx->raw_mutations);
}

static bool
bc_cfg_same_block(JitCtx const *ctx, int a, int b, int c)
{
        int ia = a >= 0 ? ctx->cfg_index[a] : -1;
        int ib = b >= 0 ? ctx->cfg_index[b] : -1;
        int ic = c >= 0 ? ctx->cfg_index[c] : -1;
        if (ia < 0 || ib < 0 || ic < 0) {
                return false;
        }
        return ctx->cfg_nodes[ia].block == ctx->cfg_nodes[ib].block
            && ctx->cfg_nodes[ia].block == ctx->cfg_nodes[ic].block;
}

static bool
bc_cfg_local_operand(BcCfgNode const *node, char const *code, int *local)
{
        switch (node->op) {
        case INSTR_LOAD_LOCAL:
        case INSTR_ASSIGN_LOCAL:
        case INSTR_TARGET_LOCAL:
                __builtin_memcpy(local, code + node->offset + 1, sizeof *local);
                return true;
        default:
                return false;
        }
}

static bool
bc_cfg_resets_raw(u8 op)
{
        switch (op) {
        case INSTR_CALL:
        case INSTR_CALL_METHOD:
        case INSTR_CALL_SELF_METHOD:
        case INSTR_CALL_STATIC_METHOD:
        case INSTR_CALL_GLOBAL:
        case INSTR_YIELD:
        case INSTR_YIELD_SOME:
        case INSTR_YIELD_NONE:
        case INSTR_THROW:
        case INSTR_RETHROW:
        case INSTR_TRY:
        case INSTR_CATCH:
        case INSTR_FINALLY:
        case INSTR_END_TRY:
                return true;
        default:
                return false;
        }
}

static bool
bc_build_cfg_blocks(JitCtx *ctx, int code_size)
{
        u8 *leaders = calloc((usize)code_size + 1, 1);
        if (leaders == NULL) {
                return false;
        }
        leaders[0] = 1;
        for (int i = 0; i < ctx->cfg_count; ++i) {
                BcCfgNode const *node = &ctx->cfg_nodes[i];
                ctx->cfg_index[node->offset] = i;
                if (node->target >= 0 && node->target <= code_size) {
                        leaders[node->target] = 1;
                        if (node->next <= code_size) {
                                leaders[node->next] = 1;
                        }
                }
        }
        int block = -1;
        for (int i = 0; i < ctx->cfg_count; ++i) {
                BcCfgNode *node = &ctx->cfg_nodes[i];
                if (leaders[node->offset]) {
                        ++block;
                }
                node->block = block;
        }
        free(leaders);
        for (int i = 0; i < ctx->cfg_count; ++i) {
                int target = ctx->cfg_nodes[i].target;
                if (target >= 0
                    && (target > code_size
                        || (target < code_size && ctx->cfg_index[target] < 0))) {
#if JIT_SCAN_LOG
                        LOGX("JIT: bad CFG target %d from %d (size %d, index %d)",
                             target, ctx->cfg_nodes[i].offset, code_size,
                             target <= code_size ? ctx->cfg_index[target] : -2);
#endif
                        return false;
                }
        }
        return true;
}

static void
bc_plan_raw_cache(JitCtx *ctx, char const *code, int code_size)
{
#ifdef TY_PROFILER
        (void)ctx;
        (void)code;
        (void)code_size;
        return;
#else
        if (!ctx->registerize
            || getenv("TY_JIT_NO_RAW_CACHE") != NULL
            || ctx->cfg_count == 0) {
                return;
        }
        Symbol **locals = vv(expr_of(ctx->func)->scope->owned);
        for (int i = 0; i < ctx->cfg_count; ++i) {
                BcCfgNode *node = &ctx->cfg_nodes[i];
                if (node->target >= 0 && node->target < node->offset) {
                        for (int j = 0; j < ctx->cfg_count; ++j) {
                                BcCfgNode const *inside = &ctx->cfg_nodes[j];
                                if (inside->offset < node->target
                                    || inside->offset > node->offset) {
                                        continue;
                                }
                                int local;
                                if (bc_cfg_local_operand(inside, code, &local)
                                    && local >= 0 && local < ctx->bound) {
                                        ctx->raw_scores[local] += 16;
                                }
                        }
                }
        }
        for (int i = 0; i + 1 < ctx->cfg_count; ++i) {
                BcCfgNode const *node = &ctx->cfg_nodes[i];
                BcCfgNode const *mut = &ctx->cfg_nodes[i + 1];
                if (node->op != INSTR_TARGET_LOCAL
                    || (mut->op != INSTR_MUT_ADD
                        && mut->op != INSTR_MUT_SUB
                        && mut->op != INSTR_MUT_MUL)
                    || node->block != mut->block) {
                        continue;
                }
                int local;
                if (bc_cfg_local_operand(node, code, &local)
                    && local >= 0 && local < ctx->bound) {
                        ctx->raw_mutations[local] += 1;
                }
        }
#if JIT_ARCH_ARM64
        static int const regs[] = { 12, 13 };
#else
        static int const regs[] = { 7, 6 };
#endif
        for (int slot = 0; slot < 2; ++slot) {
                int best = -1;
                u32 score = 0;
                for (int local = 0; local < ctx->bound; ++local) {
                        bool selected = false;
                        for (int q = 0; q < ctx->raw_count; ++q) {
                                selected |= ctx->raw_locals[q].local == local;
                        }
                        if (selected || SymbolIsCaptured(locals[local])
                            || (ctx->raw_count == 0
                                && ctx->raw_mutations[local] < 3)) {
                                continue;
                        }
                        Class *class = expected_class_of(ctx->ty, locals[local]->type);
                        if (class == NULL || class->i != CLASS_INT) {
                                continue;
                        }
                        if (ctx->raw_scores[local] > score) {
                                score = ctx->raw_scores[local];
                                best = local;
                        }
                }
                if (best < 0 || score == 0) {
                        break;
                }
                Class *class = expected_class_of(ctx->ty, locals[best]->type);
                ctx->raw_locals[ctx->raw_count++] = (BcRawLocal) {
                        .local = best,
                        .class_id = class->i,
                        .reg = regs[slot],
                };
        }

        if (ctx->raw_count == 0) {
                return;
        }
        u8 *out = calloc((usize)ctx->cfg_count, sizeof *out);
        bool changed;
        do {
                changed = false;
                for (int i = 0; i < ctx->cfg_count; ++i) {
                        BcCfgNode const *node = &ctx->cfg_nodes[i];
                        u8 state = ctx->cfg_dirty[node->offset];
                        if (bc_cfg_resets_raw(node->op)) {
                                state = 0;
                        }
                        int local;
                        if (bc_cfg_local_operand(node, code, &local)) {
                                int raw = bc_raw_slot(ctx, local);
                                if (raw >= 0) {
                                        state |= (u8)1 << raw;
                                }
                        }
                        if (out[i] != state) {
                                out[i] = state;
                                changed = true;
                        }
                        if (node->op != INSTR_JUMP
                            && node->op != INSTR_RETURN
                            && node->op != INSTR_RETURN_PRESERVE_CTX
                            && node->op != INSTR_THROW
                            && node->op != INSTR_RETHROW
                            && node->op != INSTR_HALT
                            && node->next <= code_size) {
                                ctx->cfg_dirty[node->next] |= state;
                        }
                        if (node->target >= 0 && node->target <= code_size) {
                                ctx->cfg_dirty[node->target] |= state;
                        }
                }
        } while (changed);
        free(out);
#endif
}

JitInfo *
jit_compile(Ty *ty, Value const *func)
{
#ifdef TY_PROFILER
        u64 compile_t0 = jit_wall_time();
#endif

        i32 const *info = V_INFO(*(func));
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
                .registerize    = false,
        };

        Expr const *expr = expr_of(func);
        if (expr != NULL) {
                ctx.func_type = expr->_type;
                if (expr->class != NULL) {
                        ctx.self_class = expr->class;
                        ctx.self_class_id = expr->class->i;
                }
        }

        ctx.cfg_nodes = calloc((usize)code_size + 1, sizeof *ctx.cfg_nodes);
        ctx.cfg_index = malloc(((usize)code_size + 1) * sizeof *ctx.cfg_index);
        ctx.cfg_dirty = calloc((usize)code_size + 1, sizeof *ctx.cfg_dirty);
        ctx.raw_scores = calloc((usize)bound + 1, sizeof *ctx.raw_scores);
        ctx.raw_mutations = calloc((usize)bound + 1, sizeof *ctx.raw_mutations);
        if (ctx.cfg_nodes == NULL || ctx.cfg_index == NULL
            || ctx.cfg_dirty == NULL || ctx.raw_scores == NULL
            || ctx.raw_mutations == NULL) {
                bc_free_cfg(&ctx);
                return NULL;
        }
        for (int i = 0; i <= code_size; ++i) {
                ctx.cfg_index[i] = -1;
        }

        // Pre-scan: discover jump targets, check support
        if (!bc_prescan(&ctx, bc, code_size)) {
#if JIT_SCAN_LOG
                LOGX("JIT: bail on %s", name);
#endif
                bc_free_cfg(&ctx);
                return NULL;
        }

        if (!bc_build_cfg_blocks(&ctx, code_size)) {
                bc_free_cfg(&ctx);
                return NULL;
        }
        bc_plan_raw_cache(&ctx, bc, code_size);

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
        // The resume index is passed as the second argument (BC_RESUME).
        // If non-zero, jump to a dispatch block that redirects to the
        // appropriate resume label.
        int lbl_dispatch = bc_next_label(&ctx);
        int lbl_normal_start = bc_next_label(&ctx);
        ctx.call_site_count = 0;

        asm = ctx.asm; // sync: bc_next_label may have grown pclabels

        jit_emit_cbnz(&asm, BC_RESUME, lbl_dispatch);
        jit_emit_label(&asm, lbl_normal_start);
        ctx.asm = asm;
        bc_raw_reset(&ctx);
        asm = ctx.asm;

        // Emit bytecode
        ctx.asm = asm;
        if (!bc_emit(&ctx, bc, code_size)) {
                LOG("JIT: emission failed for %s", name);
                dasm_free(&asm);
                bc_free_cfg(&ctx);
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
        // This is reached when resume_idx != 0 (checked at function entry).
        // BC_RESUME still holds the resume_idx value passed as the 2nd argument.
        if (ctx.call_site_count > 0) {
                jit_emit_label(&asm, lbl_dispatch);
                for (int i = 0; i < ctx.call_site_count; ++i) {
                        jit_emit_cmp_ri(&asm, BC_RESUME, i + 1);
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
                bc_free_cfg(&ctx);
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
                bc_free_cfg(&ctx);
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

        bc_free_cfg(&ctx);
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
