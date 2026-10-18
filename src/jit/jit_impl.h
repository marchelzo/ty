#ifndef JIT_IMPL_H_INCLUDED
#define JIT_IMPL_H_INCLUDED

#include "ty.h"
#include "jit/jit.h"

enum {
        SITE_MEMBER,
        SITE_MEMBER_SET,
        SITE_METHOD,
        SITE_ARITH,
        SITE_COMPARE,
        SITE_KIND_COUNT
};

#ifdef TY_PROFILER
typedef struct {
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
        _Atomic u64 direct_math_fast;
        _Atomic u64 direct_math_slow;
        _Atomic u64 direct_max_fast;
        _Atomic u64 direct_max_slow;
        _Atomic u64 simple_ctor_fast;
        _Atomic u64 simple_ctor_slow;
        _Atomic u64 linked_global_fast;
        _Atomic u64 linked_global_slow;
        _Atomic u64 global_jit_call_fast;
        _Atomic u64 global_jit_call_slow;
        _Atomic u64 self_call_fast;
        _Atomic u64 self_call_slow;
        _Atomic u64 self_tail_fast;
        _Atomic u64 self_tail_slow;
        _Atomic u64 numeric_pow_fast;
        _Atomic u64 numeric_pow_slow;
} JitStats;

typedef struct {
        uptr          lo;
        u32           size;
        u32           literal;
        u8           *bytes;
        LirSite      *sites;
        u32           nsites;
        char const   *bc;
        char const   *name;
        u32          *hits;
        u64           samples;
} JitImageRec;

typedef struct {
        char const  *name;
        char const  *class_name;
        Expr const  *expr;
        usize        native_size;
        u64          compile_time_ns;
        int          bc_code_size;
        bool         compact;
        JitImageRec *image;
} JitCompileRecord;

JitImageRec *
jit_image_record(LirCode const *code, char const *bc, char const *name);

void
jit_code_hit(uptr rip);

extern JitStats jit_stats;

void
jit_log_compile(JitCompileRecord rec);

JitCompileRecord const *
jit_compile_records(usize *n);

typedef void JitSlowSiteFn(void *ctx, char const *ip, char const *kind, u64 count, i32 const *classes, u64 const *counts, int n);

void
jit_slow_sites(JitSlowSiteFn *fn, void *ctx);

void
jit_stats_json(Ty *ty, FILE *f);

void
jit_site_miss(Ty *ty, void const *ra, int kind, Value const *a, Value const *b);

u64 *
jit_site_fast(char const *ip, int kind);

u64 *
jit_site_fast_base(void);

u32
jit_guard(char const *text);

char const *
jit_guard_text(u32 id);

extern bool JitStatsOn;

#define STAT(name) (                                                                     \
        JitStatsOn                                                                        \
      ? atomic_store_explicit(                                                            \
                &jit_stats.name,                                                          \
                atomic_load_explicit(&jit_stats.name, memory_order_relaxed) + 1,          \
                memory_order_relaxed                                                      \
        )                                                                                 \
      : (void)0                                                                           \
)
#else
#define STAT(name) ((void)0)
#endif

void
jit_perf_map(void *code, usize size, char const *name, Expr const *expr);

void
jit_rt_add(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_sub(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_mul(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_div(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_mod(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_neg(Ty *ty, Value *result, Value *a);

void
jit_rt_eq(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_ne(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_lt(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_le(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_gt(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_ge(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_member(Ty *ty, Value *result, Value *obj, int member_id);

void
jit_rt_try_member(Ty *ty, Value *top, int member_id);

void
jit_rt_get_member(Ty *ty, Value *top);

void
jit_rt_try_get_member(Ty *ty, Value *top);

int
jit_rt_try_tag_pop(Ty *ty, Value *val, int tag);

int
jit_rt_index_tuple(Value *tos, Value *dst, int i);

int
jit_rt_try_tuple_member(Value *tos, Value *dst, bool required, int name_id);

int
jit_rt_try_steal_tag(Ty *ty, Value *tos, Value *target);

void
jit_rt_tag_push(Ty *ty, Value *v, int tag);

int
jit_rt_try_regex(Ty *ty, Value *str, Regex *re, Value *top);

void
jit_rt_assign_regex_matches(Ty *ty, Value *match, int n);

int
jit_rt_jii(Ty *ty, Value *v, int class_id);

void
jit_rt_capture(Ty *ty, Value *local, Value **env, int env_idx);

i32
jit_rt_match_string(Value const *v, i32 table_size, char const *table);

void
jit_rt_function(Ty *ty, Value *top, char const *ip);

void
jit_rt_generator(Ty *ty, Value *top, char const *ip);

void
jit_rt_patch_env(Ty *ty, Value *top, int n);

int
jit_rt_try_index(Value *tos, Value *dst, int i, bool required);

void
jit_rt_tuple(Ty *ty, Value *top, i32 n, i32 *ids);

void
jit_rt_subscript(Ty *ty, Value *top);

void
jit_rt_safe_subscript(Ty *ty, Value *top);

int
jit_rt_truthy(Ty *ty, Value *v);

void
jit_rt_bit_and(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_bit_or(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_bit_xor(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_shl(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_shr(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_inc(Ty *ty, Value *v);

void
jit_rt_dec(Ty *ty, Value *v);

void
jit_rt_string(Ty *ty, Value *result, i32 i);

void
jit_rt_tail_loop(Value *locals, Value const *arguments, int param_count,
                 int bound, int kept);

void
jit_rt_call_global_kw(Ty *ty, Value *top, int gi, int n, int nkw, char *kw_ip);

void
jit_rt_call_kw(Ty *ty, Value *top, int n, int nkw, char *kw_ip);

void
jit_rt_call_method_kw(Ty *ty, Value *top, int z, int n, int nkw, char *kw_ip);

void
jit_rt_cmp(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_count(Ty *ty, Value *result, Value *v);

void
jit_rt_assign_subscript(Ty *ty, Value *top, int n);

void
jit_rt_array(Ty *ty, Value *result, Value *elements, int n);

void
jit_rt_array0(Ty *ty, Value *result);

void
jit_rt_array_compr(Ty *ty, Value *top, i32 idx, i32 n);

void
jit_rt_loop_iter(Ty *ty, Value *top);

int
jit_rt_loop_check(Ty *ty, int z, Value *top);

void
jit_rt_throw(Ty *ty, Value *exc);

void
jit_rt_range(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_incrange(Ty *ty, Value *result, Value *a, Value *b);

void
jit_rt_catch(Ty *ty);

void
jit_rt_rethrow_setup(Ty *ty);

void
jit_rt_finally_enter(Ty *ty, char *resume_addr);

char *
jit_rt_end_try(Ty *ty);

void
jit_rt_pop_try(Ty *ty);

int
jit_rt_tuple_rest(Ty *ty, Value *tos, i32 start);

int
jit_audit_level(void);

int
jit_rt_call_trampoline(Ty *ty, Value *out, Value *fn, int argc);

bool
jit_linkable_global(Value const *fn, int argc);

void
jit_rt_call_builtin_method(Ty *ty, Value *result, Value *self,
                           BuiltinMethod *func, int64_t vtype_and_member, int argc);

int
jit_rt_yield(Ty *ty, Value *top);

int
jit_rt_yield_some(Ty *ty, Value *top);

int
jit_rt_yield_none(Ty *ty, Value *top);

void
jit_rt_check_match(Ty *ty, Value *result, Value *value, Value *pattern);

void
jit_rt_concat_strings(Ty *ty, Value *result, Value *base, int n);

Class *
expected_class_of(Ty *ty, T2Type t);

T2Type
find_type_hint(TypeHintVector const *hints, iptr off);

BuiltinMethod *
jit_builtin_method(Class *cls, int member_id, int *value_type);

inline static void
jit_fast_frame(Ty *ty, Value const *fn, Value const *self, int argc)
{
        if (UNLIKELY(vN(ty->st->frames) >= TY_MAX_CALL_DEPTH)) {
                zP("maximum call depth exceeded");
        }
        int bound = fn->info[FUN_INFO_BOUND];
        int fp = vN(STACK) - argc;

        int needed = fp + bound;
        if (UNLIKELY((usize)needed > vC(STACK))) {
                xvR(STACK, needed + 256);
        }

        Value *base = vv(STACK) + fp;
        if (argc < bound) {
                NilStackRange(ty, fp + argc, bound - argc);
        }
        vN(STACK) = needed;

        if (self != NULL) {
                int np = fn->info[FUN_INFO_PARAM_COUNT];
                base[np] = *self;
        }

        int irest   = rest_idx_of(fn);
        int ikwargs = kwargs_idx_of(fn);

        if (UNLIKELY(irest != ikwargs)) {
                if (irest >= 0) {
                        base[irest] = ARRAY(vAu());
                }
                if (ikwargs >= 0) {
                        base[ikwargs] = DICT(dict_xnew(ty));
                }
        }

        xvP(ty->st->frames, ((Frame){ .fp = fp, .f = *fn, .ip = ty->ip }));
        xvP(ty->st->calls, ty->ip);

        vvL(ty->st->frames)->f.type = VALUE_NATIVE_FUNCTION;
        vvL(ty->st->frames)->f.tags = 0;

        ty->ip = &JIT;

        CO_LOG("jit_fast_frame", TERM(33;1), "");
}

inline static void
jit_call_method_at(Ty *ty, Value *top, int z, int n, int nkw, char *kw_ip, bool maybe)
{
        vN(STACK) = top - vv(STACK);
        char *saved = ty->ip;
        ty->ip = kw_ip;
        CallMethod(ty, z, n, nkw, maybe, true);
        ty->ip = saved;
}

JitFn *
jit_lower(Ty *ty, Value const *f);

#endif
