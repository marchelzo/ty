#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>

#include "ty.h"
#include "value.h"
#include "ast.h"
#include "types2.h"
#include "scope.h"
#include "class.h"
#include "jit/jit.h"
#include "jit/lir.h"
#include "log.h"
#include "vm.h"
#include "compiler.h"
#include "cffi.h"
#include "str.h"
#include "array.h"
#include "dict.h"
#include "set.h"
#include "heap.h"
#include "blob.h"
#include "queue.h"
#include "itable.h"
#include "inline.h"
#include "operators.h"
#include "compiler.h"
#include "jit_impl.h"

char JIT;

static void
lir_arity_error(Ty *ty, i32 expected, i32 actual)
{
        zP("jit: expected %d arguments but got %d", expected, actual);
}

static void
lir_arg_type_error(Ty *ty, i32 index, LirType type, Value const *v)
{
        zP("jit: argument %d has an invalid value for C type %d: %s", index + 1, type, VSC(v));
}

static void
lir_interpret_error(Ty *ty, LirError const *error)
{
        zP("jit interpreter: %s", error->message);
}

inline static bool
within(uptr p, uptr base, uptr end)
{
        return (base != 0) && (p >= base) && (p < end);
}

static void *
lir_rebase(Ty *ty, LirEntryFrame *frame)
{
        uptr base = (uptr)frame->base;
        uptr end  = base + frame->capacity * sizeof (Value);
        uptr args = (uptr)frame->args;
        uptr out  = (uptr)frame->out;

        if (within(args, base, end + 1)) {
                frame->args = (void *)((uptr)vv(ty->stack) + args - base);
        }

        if (within(out, base, end)) {
                frame->out = (void *)((uptr)vv(ty->stack) + out - base);
        }

        frame->base     = vv(ty->stack);
        frame->capacity = vC(ty->stack);

        return frame->out;
}

static void *
lir_ptr_from(Ty *ty, LirEntryFrame *frame, i32 index)
{
        Value v = frame->args[index];
        void *p;

        if (frame->base == NULL) {
                frame->base     = vv(ty->stack);
                frame->capacity = vC(ty->stack);
        }

        if (!ptr_from_ty(ty, &v, &p)) {
                lir_arg_type_error(ty, index, LT_PTR, &v);
        }

        lir_rebase(ty, frame);

        return p;
}

static void *
lir_ref_from(Ty *ty, Value const *v, i32 index)
{
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_ARRAY:  return v->array;
        case VALUE_DICT:   return v->dict;
        case VALUE_SET:    return v->set;
        case VALUE_HEAP:   return v->heap;
        case VALUE_BLOB:   return v->blob;
        case VALUE_OBJECT: return v->object;
        case VALUE_TUPLE:  return v->items;
        case VALUE_NIL:    return NULL;

        case VALUE_STRING:
                if (v->str0 == NULL || v->ro) {
                        return value_string_clone(ty, v->str, v->bytes);
                }
                return v->str0;

        default:
                lir_arg_type_error(ty, index, LT_REF, v);
                return NULL;
        }
}

static void
lir_reserve(Ty *ty, LirEntryFrame *frame, u32 n)
{
        usize count = vN(ty->stack);

        frame->base     = vv(ty->stack);
        frame->capacity = vC(ty->stack);
        frame->top      = count;

        if (n > (SIZE_MAX / sizeof (Value)) - count) {
                zP("jit: value stack is too large");
        }

        xvR(ty->stack, count + n);
        lir_rebase(ty, frame);

        if (n != 0) {
                memset(vZ(ty->stack), 0, n * sizeof (Value));
        }

        vN(ty->stack) = count + n;
}

static Value *
lir_restore(Ty *ty, LirEntryFrame *frame)
{
        lir_rebase(ty, frame);
        vN(ty->stack) = frame->top;
        return frame->out;
}

static void
lir_unlock(Ty *ty)
{
        UnlockTy();
}

static void
lir_lock(Ty *ty)
{
        LockTy();
}

static i32
lir_vm_poll(Ty *ty, Value *top, void const *info)
{
        return vm_jit_handle_interrupt(ty, top, info);
}

static LirRuntime const LirVM = {
        .interrupt       = &JitInterruptFlag,
        .poll            = lir_vm_poll,
        .current_ty      = GetMyTy,
        .arity_error     = lir_arity_error,
        .arg_type_error  = lir_arg_type_error,
        .ptr_from        = lir_ptr_from,
        .ref_from        = lir_ref_from,
        .reserve         = lir_reserve,
        .restore         = lir_restore,
        .unlock          = lir_unlock,
        .lock            = lir_lock,
        .interpret_error = lir_interpret_error
};

static void
jit_dump_code(void const *code, usize size, char const *dir, char const *name)
{
        char path[4096];

        ty_snprintf(path, sizeof path, "%s/%s@%lx.bin", dir, name, (unsigned long)(uptr)code);

        FILE *out = fopen(path, "wb");

        if (out != NULL) {
                fwrite(code, 1, size, out);
                fclose(out);
        }
}

void
jit_perf_map(void *code, usize size, char const *name, Expr const *expr)
{
        char const *map  = getenv("TY_JIT_PERF_MAP");
        char const *dir  = getenv("TY_JIT_BIN");
        bool        perf = (map != NULL) && s_eq(map, "1");

        if (!perf && dir == NULL) {
                return;
        }

        char const *mod = (expr != NULL && expr->mod != NULL) ? expr->mod->name : "";
        char const *cls = (expr != NULL && expr->class != NULL) ? expr->class->name : "";
        char        qualified[strlen(mod) + strlen(cls) + strlen(name) + 3];

        ty_snprintf(
                qualified,
                sizeof qualified,
                "%s%s%s%s%s",
                mod,
                (*mod != '\0') ? "." : "",
                cls,
                (*cls != '\0') ? "." : "",
                name
        );

        if (perf) {
                jm_perf(code, size, qualified);
        }

        if (dir != NULL) {
                jit_dump_code(code, size, dir, qualified);
        }
}

char const *
jit_frame_ip(Frame const *frame, char const *ip)
{
        if (ip != &JIT || frame == NULL) {
                return ip;
        }

        char const *entry = frame->jit_code != NULL ? frame->jit_code : jit_of(&frame->f);
        char const *bc = code_of(&frame->f);
        if (entry == NULL || jit_pending(entry)) {
                return bc + 1;
        }

        LirImage const *code = (void const *)(entry - sizeof *code);
        LirSite const *sites = (void const *)(entry + code->table);

        if (frame->jit_pc != NULL) {
                uptr pc = *frame->jit_pc - (uptr)entry;
                u32 lo = 0;
                u32 hi = code->nsites;
                while (lo < hi) {
                        u32 mid = lo + (hi - lo) / 2;
                        if (sites[mid].pc < pc) {
                                lo = mid + 1;
                        } else {
                                hi = mid;
                        }
                }
                if (lo < code->nsites && sites[lo].pc == pc) {
                        return bc + sites[lo].tag;
                }
        } else if (frame->jit_resume > 0 && frame->jit_resume <= code->nresume) {
                u32 const *resumes = (void const *)(sites + code->nsites);
                return bc + resumes[frame->jit_resume - 1];
        }

        return bc + 1;
}

JitStats jit_stats;
bool JitStatsOn = false;

typedef enum {
        JIT_OPT_INLINE_GETTER,
        JIT_OPT_INLINE_METHOD,
        JIT_OPT_INLINE_SELF_METHOD,
        JIT_OPT_INLINE_GLOBAL,
        JIT_OPT_INLINE_OPERATOR,
        JIT_OPT_FUSE_LOCAL_ARRAY_SWAP,
        JIT_OPT_FUSE_LOCAL_ARRAY_GET_ASSIGN,
        JIT_OPT_FUSE_LOCAL_ARRAY_STORE_POP,
        JIT_OPT_FUSE_LOCAL_ARRAY_GET,
        JIT_OPT_FUSE_RANGE_GUARD,
        JIT_OPT_FUSE_LOCAL_CONDITION,
        JIT_OPT_FUSE_LOCAL_SUBSCRIPT,
        JIT_OPT_FUSE_CONST_SUBSCRIPT,
        JIT_OPT_FUSE_LOCAL_JCMP,
        JIT_OPT_FUSE_LOCAL_IMM_MUT,
        JIT_OPT_FUSE_LOCAL_SOURCE_MUT,
        JIT_OPT_BUILTIN_COUNT,
        JIT_OPT_PRIMITIVE_MEMBER,
        JIT_OPT_SQRT,
        JIT_OPT_KNOWN_MEMBER_READ,
        JIT_OPT_DYNAMIC_MEMBER_READ,
        JIT_OPT_MEMBER_WRITE,
        JIT_OPT_MEMBER_MUT,
        JIT_OPT_SELF_MEMBER_READ,
        JIT_OPT_SELF_MEMBER_WRITE,
        JIT_OPT_SELF_MEMBER_MUT,
        JIT_OPT_DIRECT_BUILTIN,
        JIT_OPT_DIRECT_MATH,
        JIT_OPT_DIRECT_MAX,
        JIT_OPT_SIMPLE_CTOR,
        JIT_OPT_LINKED_GLOBAL,
        JIT_OPT_SELF_CALL,
        JIT_OPT_SELF_TAIL,
        JIT_OPT_BUILTIN_METHOD,
        JIT_OPT_BAKED_METHOD,
        JIT_OPT_NUMERIC_POW,
        JIT_OPT_COUNT
} JitOptimization;

static char const *jit_opt_names[JIT_OPT_COUNT] = {
        [JIT_OPT_INLINE_GETTER]          = "inline getter",
        [JIT_OPT_INLINE_METHOD]          = "inline method call",
        [JIT_OPT_INLINE_SELF_METHOD]     = "inline self method call",
        [JIT_OPT_INLINE_GLOBAL]          = "inline global call",
        [JIT_OPT_INLINE_OPERATOR]        = "inline operator",
        [JIT_OPT_FUSE_LOCAL_ARRAY_SWAP] = "fuse local array swap",
        [JIT_OPT_FUSE_LOCAL_ARRAY_GET_ASSIGN] = "fuse local array get + assign",
        [JIT_OPT_FUSE_LOCAL_ARRAY_STORE_POP]  = "fuse local array store + pop",
        [JIT_OPT_FUSE_LOCAL_ARRAY_GET]   = "fuse local array get",
        [JIT_OPT_FUSE_RANGE_GUARD]       = "fuse range guard",
        [JIT_OPT_FUSE_LOCAL_CONDITION]   = "fuse local condition",
        [JIT_OPT_FUSE_LOCAL_SUBSCRIPT]  = "fuse local subscript",
        [JIT_OPT_FUSE_CONST_SUBSCRIPT]  = "fuse constant subscript",
        [JIT_OPT_FUSE_LOCAL_JCMP]        = "fuse local integer branch compare",
        [JIT_OPT_FUSE_LOCAL_IMM_MUT]     = "fuse local immediate mutation",
        [JIT_OPT_FUSE_LOCAL_SOURCE_MUT]  = "fuse local source mutation",
        [JIT_OPT_BUILTIN_COUNT]          = "specialize builtin count",
        [JIT_OPT_PRIMITIVE_MEMBER]       = "specialize primitive member",
        [JIT_OPT_SQRT]                   = "emit direct sqrt",
        [JIT_OPT_KNOWN_MEMBER_READ]      = "specialize known member read",
        [JIT_OPT_DYNAMIC_MEMBER_READ]    = "emit dynamic member read cache",
        [JIT_OPT_MEMBER_WRITE]           = "specialize member write",
        [JIT_OPT_MEMBER_MUT]             = "specialize member numeric mutation",
        [JIT_OPT_SELF_MEMBER_READ]       = "specialize self member read",
        [JIT_OPT_SELF_MEMBER_WRITE]      = "specialize self member write",
        [JIT_OPT_SELF_MEMBER_MUT]        = "specialize self member numeric mutation",
        [JIT_OPT_DIRECT_BUILTIN]         = "emit direct builtin call",
        [JIT_OPT_DIRECT_MATH]            = "emit direct sin/cos",
        [JIT_OPT_DIRECT_MAX]             = "emit direct max",
        [JIT_OPT_SIMPLE_CTOR]            = "emit simple constructor",
        [JIT_OPT_LINKED_GLOBAL]          = "emit linked global call",
        [JIT_OPT_SELF_CALL]              = "emit direct self call",
        [JIT_OPT_SELF_TAIL]              = "emit self tail-call loop",
        [JIT_OPT_BUILTIN_METHOD]         = "emit builtin method call",
        [JIT_OPT_BAKED_METHOD]           = "emit baked method call",
        [JIT_OPT_NUMERIC_POW]            = "emit numeric pow",
};

static _Atomic u64 jit_opt_sites[JIT_OPT_COUNT];
static _Atomic u64 jit_opt_units[JIT_OPT_COUNT];

static vec(JitCompileRecord) jit_compile_log = {0};
static u64 jit_total_compile_ns = 0;
static usize jit_total_native_bytes = 0;
static TySpinLock JitLogMutex;

void
jit_log_compile(JitCompileRecord rec)
{
        TySpinLockLock(&JitLogMutex);
        jit_total_compile_ns   += rec.compile_time_ns;
        jit_total_native_bytes += rec.native_size;
        xvP(jit_compile_log, rec);
        TySpinLockUnlock(&JitLogMutex);
}

static vec(JitImageRec *) Images;

bool JitDetail;

JitImageRec *
jit_image_new(LirCode const *code, char const *bc, char const *name, JitNotes notes)
{
        JitImageRec *img = calloc(1, sizeof *img);

        if (img == NULL || code->body == NULL) {
                free(img);
                free(notes.notes);
                free(notes.text);
                return NULL;
        }

        img->lo      = (uptr)code->body;
        img->size    = (u32)code->size;
        img->literal = (code->literal_pool != NULL)
                     ? (u32)((char const *)code->literal_pool - (char const *)code->body)
                     : (u32)code->size;
        img->bytes   = malloc(code->size);
        img->sites   = malloc((code->nsites + 1) * sizeof *img->sites);
        img->nsites  = code->nsites;
        img->notes   = notes;
        img->bc      = bc;
        img->name    = name;

        memcpy(img->bytes, code->body, code->size);
        memcpy(img->sites, code->sites, code->nsites * sizeof *img->sites);

        return img;
}

void
jit_image_free(JitImageRec *img)
{
        if (img != NULL) {
                free(img->bytes);
                free(img->sites);
                free(img->hits);
                free(img->notes.notes);
                free(img->notes.text);
                free(img);
        }
}

JitImageRec *
jit_image_record(LirCode const *code, char const *bc, char const *name, JitNotes notes)
{
        JitImageRec *img = jit_image_new(code, bc, name, notes);

        if (img == NULL) {
                return NULL;
        }

        TySpinLockLock(&JitLogMutex);

        usize lo = 0;
        usize hi = vN(Images);

        while (lo < hi) {
                usize mid = lo + (hi - lo) / 2;
                if (v__(Images, mid)->lo < img->lo) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        while (lo > 0 && v__(Images, lo - 1)->lo + v__(Images, lo - 1)->size > img->lo) {
                lo -= 1;
                v__(Images, lo) = NULL;
        }

        usize end = lo;

        while (
                (end < vN(Images))
             && (v__(Images, end) == NULL || v__(Images, end)->lo < img->lo + img->size)
        ) {
                end += 1;
        }

        if (end > lo) {
                memmove(v_(Images, lo), v_(Images, end), (vN(Images) - end) * sizeof (JitImageRec *));
                vN(Images) -= end - lo;
        }

        vec_nogc_insert(Images, img, lo);

        TySpinLockUnlock(&JitLogMutex);

        return img;
}

void
jit_code_hit(uptr rip)
{
        TySpinLockLock(&JitLogMutex);

        usize lo = 0;
        usize hi = vN(Images);

        while (lo < hi) {
                usize mid = lo + (hi - lo) / 2;
                if (v__(Images, mid)->lo <= rip) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        if (lo > 0) {
                JitImageRec *img = v__(Images, lo - 1);
                if (rip < img->lo + img->size) {
                        if (img->hits == NULL) {
                                img->hits = calloc(img->size, sizeof *img->hits);
                        }
                        if (img->hits != NULL) {
                                img->hits[rip - img->lo] += 1;
                        }
                        img->samples += 1;
                }
        }

        TySpinLockUnlock(&JitLogMutex);
}

static char const *
image_name(uptr addr)
{
        usize lo = 0;
        usize hi = vN(Images);

        while (lo < hi) {
                usize mid = lo + (hi - lo) / 2;
                if (v__(Images, mid)->lo <= addr) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        if (lo > 0 && addr == v__(Images, lo - 1)->lo) {
                return v__(Images, lo - 1)->name;
        }

        return NULL;
}

static void
json_str(FILE *f, char const *s);

static void
image_sym(FILE *f, uptr *seen, int *nseen, uptr addr)
{
        if (*nseen >= 512) {
                return;
        }

        for (int i = 0; i < *nseen; ++i) {
                if (seen[i] == addr) {
                        return;
                }
        }

        char const *name = image_name(addr);

        if (name == NULL) {
                name = prof_symbolize(addr);
        }

        if (name == NULL) {
                return;
        }

        fprintf(f, "%s[\"0x%llx\",", (*nseen > 0) ? "," : "", (unsigned long long)addr);
        json_str(f, name);
        fputc(']', f);

        seen[(*nseen)++] = addr;
}

static char const *const RoleNames[] = {
        [JIT_ROLE_CODE]     = "code",
        [JIT_ROLE_PROLOGUE] = "prologue",
        [JIT_ROLE_MOVES]    = "moves",
        [JIT_ROLE_GUARD]    = "guard",
        [JIT_ROLE_SLOW]     = "slow",
        [JIT_ROLE_DEOPT]    = "deopt",
        [JIT_ROLE_TIERUP]   = "tierup",
        [JIT_ROLE_POLL]     = "poll",
        [JIT_ROLE_ENTRY]    = "entry",
        [JIT_ROLE_EDGE]     = "edge",
        [JIT_ROLE_REBASE]   = "rebase",
        [JIT_ROLE_EPILOGUE] = "epilogue",
        [JIT_ROLE_THUNK]    = "thunk",
        [JIT_ROLE_DATA]     = "data"
};

static int
bc_line(Ty *ty, JitImageRec const *img, u32 tag, bool exact)
{
        Expr const *e = (tag != 0) ? compiler_find_expr(ty, img->bc + tag - exact) : NULL;
        return (e != NULL) ? (int)e->start.line + 1 : 0;
}

static void
image_json(Ty *ty, FILE *f, JitImageRec const *img, bool code)
{
        fprintf(f, ",\"samples\":%llu", (unsigned long long)img->samples);

        if (!code) {
                return;
        }

        fprintf(f, ",\"base\":\"0x%llx\",\"literal\":%u,\"code\":\"", (unsigned long long)img->lo, img->literal);

        for (u32 i = 0; i < img->size; ++i) {
                fprintf(f, "%02x", img->bytes[i]);
        }

        fputs("\",\"sites\":[", f);

        int last = -1;
        bool first = true;
        bool noted = (img->notes.n > 0);
        u32 nsites = noted ? img->notes.n : img->nsites;

        for (u32 i = 0; i < nsites; ++i) {
                u32 pc   = noted ? img->notes.notes[i].off : img->sites[i].pc;
                u32 tag  = noted ? img->notes.notes[i].bc : img->sites[i].tag;
                int line = bc_line(ty, img, tag, noted);
                if (line == 0 || line == last) {
                        continue;
                }
                fprintf(f, "%s[%u,%d]", first ? "" : ",", pc, line);
                last = line;
                first = false;
        }

        fputs("],\"notes\":[", f);

        byte_vector op = {0};
        u32 bc = 0;

        for (u32 i = 0; i < img->notes.n; ++i) {
                JitNote const *n = &img->notes.notes[i];
                fprintf(f, "%s[%u,%d,", (i > 0) ? "," : "", n->off, (int)n->bc - 1);
                if (n->bc != 0 && n->bc != bc) {
                        v0(op);
                        json_str(f, DumpInstruction(ty, &op, img->bc + n->bc - 1));
                } else {
                        fputs("null", f);
                }
                fputc(',', f);
                json_str(f, RoleNames[n->role]);
                fputc(',', f);
                if (n->note != 0) {
                        json_str(f, img->notes.text + n->note);
                } else {
                        fputs("null", f);
                }
                fputc(']', f);
                bc = (n->bc != 0) ? n->bc : bc;
        }

        xvF(op);

        fputs("],\"hits\":[", f);

        first = true;

        for (u32 i = 0; img->hits != NULL && i < img->size; ++i) {
                if (img->hits[i] != 0) {
                        fprintf(f, "%s[%u,%u]", first ? "" : ",", i, img->hits[i]);
                        first = false;
                }
        }

        fputs("],\"syms\":[", f);

        uptr seen[512];
        int nseen = 0;

        for (u32 i = 0; i + 8 <= img->literal; ++i) {
                u64 imm;
                memcpy(&imm, img->bytes + i, sizeof imm);
                if (imm > 0x10000 && (imm >> 48) == 0) {
                        image_sym(f, seen, &nseen, (uptr)imm);
                }
        }

        for (u32 i = 0; i + 5 <= img->literal; ++i) {
                if (img->bytes[i] == 0xE8 || img->bytes[i] == 0xE9) {
                        i32 rel;
                        memcpy(&rel, img->bytes + i + 1, sizeof rel);
                        image_sym(f, seen, &nseen, img->lo + i + 5 + (iptr)rel);
                }
        }

        fputc(']', f);
}

void
jit_record_json(Ty *ty, FILE *f, JitCompileRecord const *r, bool code)
{
        Expr const *e = r->expr;

        fputs("{\"class\":", f);
        json_str(f, r->class_name);
        fputs(",\"name\":", f);
        json_str(f, r->name);
        fputs(",\"file\":", f);
        json_str(f, (e != NULL && e->mod != NULL && e->mod->path != NULL) ? e->mod->path : "");
        fprintf(f, ",\"line\":%d", (e != NULL) ? (int)e->start.line + 1 : 0);
        fprintf(
                f,
                ",\"bc\":%d,\"native\":%zu,\"ns\":%llu,\"tier\":%d",
                r->bc_code_size,
                r->native_size,
                (unsigned long long)r->compile_time_ns,
                r->compact ? 1 : 2
        );

        if (r->image != NULL) {
                image_json(ty, f, r->image, code);
        }

        fputc('}', f);
}

char *
jit_inspect_json(Ty *ty, Value const *func, bool compact, char *why, usize n)
{
        JitImageRec *img = jit_inspect(ty, func, compact, why, n);

        if (img == NULL) {
                return NULL;
        }

        Expr const *expr = !from_eval(func) ? expr_of(func) : NULL;
        char       *out  = NULL;
        usize       len  = 0;
        FILE       *f    = open_memstream(&out, &len);

        if (f != NULL) {
                jit_record_json(ty, f, &(JitCompileRecord) {
                        .name         = name_of(func),
                        .class_name   = (expr != NULL && expr->class != NULL) ? expr->class->name : "",
                        .expr         = expr,
                        .native_size  = img->size,
                        .bc_code_size = code_size_of(func),
                        .compact      = compact,
                        .image        = img
                }, true);
                fclose(f);
        }

        jit_image_free(img);

        return out;
}

JitCompileRecord const *
jit_compile_records(usize *n)
{
        *n = vN(jit_compile_log);
        return vv(jit_compile_log);
}

static int
jit_compile_cmp(void const *a, void const *b)
{
        u64 ta = ((JitCompileRecord const *)a)->compile_time_ns;
        u64 tb = ((JitCompileRecord const *)b)->compile_time_ns;
        return (tb > ta) - (tb < ta);
}

static char const *site_kind_names[] = {
        [SITE_MEMBER]     = "member access",
        [SITE_MEMBER_SET] = "member assignment",
        [SITE_METHOD]     = "method call",
        [SITE_ARITH]      = "arithmetic",
        [SITE_COMPARE]    = "comparison",
};

#define SITE_TABLE_SIZE 8192
#define SITE_TYPES      8
#define SITE_PROBES     32

typedef struct {
        char const *ip;
        u8          kind;
        bool        inl;
        u64        *fast;
        _Atomic u64 miss;
        struct {
                i32         a;
                i32         b;
                _Atomic u64 n;
        } types[SITE_TYPES];
} JitSite;

typedef struct {
        void const *ra;
        u8          kind;
        JitSite    *site;
} JitSiteRef;

static JitSite    site_table[SITE_TABLE_SIZE];
static u64        site_fast[SITE_TABLE_SIZE];
static int        site_nfast;

static JitSite *
site_lookup(Ty *ty, void const *ra, int kind);
static JitSiteRef site_refs[SITE_TABLE_SIZE];
static TySpinLock SiteLock;

inline static void
bump(_Atomic u64 *n)
{
        atomic_store_explicit(n, atomic_load_explicit(n, memory_order_relaxed) + 1, memory_order_relaxed);
}

inline static uptr
site_hash(void const *p, int kind)
{
        return (((uptr)p >> 1) * 2654435761u + (uptr)kind * 40503u) & (SITE_TABLE_SIZE - 1);
}

static JitSite *
site_at(char const *ip, int kind)
{
        uptr     h    = site_hash(ip, kind);
        JitSite *site = NULL;

        TySpinLockLock(&SiteLock);

        for (int i = 0; i < SITE_PROBES; ++i) {
                JitSite *s = &site_table[(h + i) & (SITE_TABLE_SIZE - 1)];

                if (s->ip == ip && s->kind == kind) {
                        site = s;
                        break;
                }

                if (s->ip == NULL) {
                        s->kind = kind;
                        s->ip   = ip;
                        site    = s;
                        break;
                }
        }

        TySpinLockUnlock(&SiteLock);

        return site;
}

static _Thread_local struct {
        void const *ra;
        u8          kind;
        JitSite    *site;
} site_cache[64];

static JitSite *
site_of(Ty *ty, void const *ra, int kind)
{
        uptr c = (((uptr)ra >> 2) ^ (uptr)kind) & 63;

        if (site_cache[c].ra == ra && site_cache[c].kind == kind) {
                return site_cache[c].site;
        }

        JitSite *site = site_lookup(ty, ra, kind);

        site_cache[c].ra   = ra;
        site_cache[c].kind = kind;
        site_cache[c].site = site;

        return site;
}

static JitSite *
site_lookup(Ty *ty, void const *ra, int kind)
{
        uptr h = site_hash(ra, kind);

        for (int i = 0; i < SITE_PROBES; ++i) {
                JitSiteRef *r   = &site_refs[(h + i) & (SITE_TABLE_SIZE - 1)];
                void const *key = __atomic_load_n(&r->ra, __ATOMIC_ACQUIRE);

                if (key == NULL) {
                        break;
                }

                if (key == ra && r->kind == kind) {
                        return r->site;
                }
        }

        char const *ip   = prof_jit_ip(ty, ra);
        JitSite    *site = (ip != NULL) ? site_at(ip, kind) : NULL;

        if (site == NULL) {
                return NULL;
        }

        TySpinLockLock(&SiteLock);

        for (int i = 0; i < SITE_PROBES; ++i) {
                JitSiteRef *r = &site_refs[(h + i) & (SITE_TABLE_SIZE - 1)];

                if (r->ra == ra && r->kind == kind) {
                        break;
                }

                if (r->ra == NULL) {
                        r->kind = kind;
                        r->site = site;
                        __atomic_store_n(&r->ra, ra, __ATOMIC_RELEASE);
                        break;
                }
        }

        TySpinLockUnlock(&SiteLock);

        return site;
}

static void
site_type(JitSite *s, i32 a, i32 b)
{
        int slot = 0;
        u64 low  = UINT64_MAX;

        for (int i = 0; i < SITE_TYPES; ++i) {
                u64 n = s->types[i].n;

                if (n > 0 && s->types[i].a == a && s->types[i].b == b) {
                        bump(&s->types[i].n);
                        return;
                }

                if (n < low) {
                        low  = n;
                        slot = i;
                }
        }

        s->types[slot].a = a;
        s->types[slot].b = b;
        s->types[slot].n = 1;
}

void
jit_site_miss(Ty *ty, void const *ra, int kind, Value const *a, Value const *b)
{
        if (!JitStatsOn) {
                return;
        }

        JitSite *s = site_of(ty, ra, kind);

        if (s == NULL) {
                return;
        }

        u64 n = s->miss;

        atomic_store_explicit(&s->miss, n + 1, memory_order_relaxed);

        if (n < 64 || (n & 7) == 0) {
                site_type(s, (a != NULL) ? ClassOf(a) : -1, (b != NULL) ? ClassOf(b) : -1);
        }
}

static vec(char *) Guards;
static TySpinLock GuardLock;

u32
jit_guard(char const *text)
{
        TySpinLockLock(&GuardLock);
        xvP(Guards, strdup(text));
        u32 id = vN(Guards);
        TySpinLockUnlock(&GuardLock);

        return id;
}

char const *
jit_guard_text(u32 id)
{
        char const *text = NULL;

        TySpinLockLock(&GuardLock);
        if (id > 0 && id <= vN(Guards)) {
                text = v__(Guards, id - 1);
        }
        TySpinLockUnlock(&GuardLock);

        return text;
}

u64 *
jit_site_fast_base(void)
{
        return site_fast;
}

u64 *
jit_site_fast(char const *ip, int kind)
{
        JitSite *s = site_at(ip, kind);

        if (s == NULL) {
                return NULL;
        }

        TySpinLockLock(&SiteLock);

        if (s->fast == NULL && site_nfast < SITE_TABLE_SIZE) {
                s->fast = &site_fast[site_nfast++];
        }

        s->inl = (s->fast != NULL);

        TySpinLockUnlock(&SiteLock);

        return s->fast;
}

static int
site_cmp(void const *a, void const *b)
{
        JitSite const *x = a;
        JitSite const *y = b;
        u64 mx = x->miss;
        u64 my = y->miss;
        if (mx != my) {
                return (my > mx) - (my < mx);
        }
        u64 fx = (x->fast != NULL) ? *x->fast : 0;
        u64 fy = (y->fast != NULL) ? *y->fast : 0;
        return (fy > fx) - (fy < fx);
}

static void
json_str(FILE *f, char const *s)
{
        fputc('"', f);

        for (; s != NULL && *s != '\0'; ++s) {
                u8 c = *s;
                if (c == '"' || c == '\\') {
                        fprintf(f, "\\%c", c);
                } else if (c < 0x20 || c == '<') {
                        fprintf(f, "\\u%04x", c);
                } else {
                        fputc(c, f);
                }
        }

        fputc('"', f);
}

static bool
json_path(FILE *f, bool first, char const *op, u64 fast, u64 slow, bool counted)
{
        if (fast + slow == 0) {
                return first;
        }

        fprintf(f, "%s{\"op\":", first ? "" : ",");
        json_str(f, op);

        if (counted) {
                fprintf(f, ",\"fast\":%llu", (unsigned long long)fast);
        } else {
                fputs(",\"fast\":null", f);
        }

        fprintf(f, ",\"slow\":%llu}", (unsigned long long)slow);

        return false;
}

void
jit_stats_json(Ty *ty, FILE *f)
{
        TySpinLockLock(&JitLogMutex);

        qsort(vv(jit_compile_log), vN(jit_compile_log), sizeof (JitCompileRecord), jit_compile_cmp);

        fprintf(
                f,
                "{\"compile_ns\":%llu,\"native_bytes\":%zu,\"compiled\":[",
                (unsigned long long)jit_total_compile_ns,
                jit_total_native_bytes
        );

        usize budget = 1u << 20;

        for (usize i = 0; i < vN(jit_compile_log); ++i) {
                JitCompileRecord const *r = v_(jit_compile_log, i);
                bool code = (r->image != NULL)
                         && ((r->image->samples > 0) || (r->image->size <= budget));
                if (code) {
                        budget -= min(budget, (usize)r->image->size);
                }
                if (i > 0) {
                        fputc(',', f);
                }
                jit_record_json(ty, f, r, code);
        }

        TySpinLockUnlock(&JitLogMutex);

        fputs("],\"plans\":[", f);

        bool first = true;

        for (int i = 0; i < JIT_OPT_COUNT; ++i) {
                if (jit_opt_sites[i] == 0) {
                        continue;
                }
                fprintf(f, "%s{\"name\":", first ? "" : ",");
                json_str(f, jit_opt_names[i]);
                fprintf(
                        f,
                        ",\"sites\":%llu,\"units\":%llu}",
                        (unsigned long long)jit_opt_sites[i],
                        (unsigned long long)jit_opt_units[i]
                );
                first = false;
        }

        u64 fast[SITE_KIND_COUNT] = {0};
        u64 miss[SITE_KIND_COUNT] = {0};
        u64 slow[SITE_KIND_COUNT] = {0};
        JitSite *sorted = malloc(SITE_TABLE_SIZE * sizeof *sorted);
        int n = 0;

        for (int i = 0; i < SITE_TABLE_SIZE; ++i) {
                JitSite const *site = &site_table[i];
                u64 hits = (site->fast != NULL) ? *site->fast : 0;
                if (site->ip != NULL && (hits + site->miss) > 0) {
                        fast[site->kind] += hits;
                        if (site->inl) {
                                miss[site->kind] += site->miss;
                        } else {
                                slow[site->kind] += site->miss;
                        }
                        sorted[n++] = *site;
                }
        }

        JitStats const *st = &jit_stats;

        fputs("],\"paths\":[", f);

        first = true;
        first = json_path(f, first, "member access",     fast[SITE_MEMBER],     miss[SITE_MEMBER],     true);
        first = json_path(f, first, "member access (no inline path)", 0,       slow[SITE_MEMBER],     false);
        first = json_path(f, first, "member assignment", fast[SITE_MEMBER_SET], miss[SITE_MEMBER_SET], true);
        first = json_path(f, first, "member assignment (no inline path)", 0,   slow[SITE_MEMBER_SET], false);
        first = json_path(f, first, "method call",       st->call_method_baked + st->call_method_builtin, slow[SITE_METHOD] + miss[SITE_METHOD], true);
        first = json_path(f, first, "arithmetic",        0,                     slow[SITE_ARITH] + miss[SITE_ARITH],     false);
        first = json_path(f, first, "comparison",        0,                     slow[SITE_COMPARE] + miss[SITE_COMPARE], false);

        qsort(sorted, n, sizeof sorted[0], site_cmp);

        fputs("],\"sites\":[", f);

        for (int i = 0; i < n && i < 500; ++i) {
                JitSite const *site = &sorted[i];
                Expr const *e = compiler_find_expr(ty, site->ip - 1);
                Expr const *fe = compiler_find_func(ty, site->ip - 1);
                fprintf(f, "%s{\"kind\":", (i > 0) ? "," : "");
                json_str(f, site_kind_names[site->kind]);
                fprintf(
                        f,
                        ",\"fast\":%llu,\"miss\":%llu,\"inline\":%s,\"file\":",
                        (unsigned long long)((site->fast != NULL) ? *site->fast : 0),
                        (unsigned long long)site->miss,
                        site->inl ? "true" : "false"
                );
                json_str(f, (e != NULL && e->mod != NULL) ? e->mod->path : "");
                fprintf(f, ",\"line\":%d,\"col\":%d,\"func\":", (e != NULL) ? (int)e->start.line + 1 : 0, (e != NULL) ? (int)e->start.col + 1 : 0);
                if (fe != NULL && fe->name != NULL && fe->class != NULL) {
                        char name[256];
                        ty_snprintf(name, sizeof name, "%s.%s", fe->class->name, fe->name);
                        json_str(f, name);
                } else {
                        json_str(f, (fe != NULL && fe->name != NULL) ? fe->name : "");
                }
                fputs(",\"types\":[", f);
                bool tfirst = true;
                for (int j = 0; j < SITE_TYPES; ++j) {
                        if (site->types[j].n == 0) {
                                continue;
                        }
                        fputs(tfirst ? "[" : ",[", f);
                        json_str(f, (site->types[j].a >= 0) ? class_name(ty, site->types[j].a) : "");
                        fputc(',', f);
                        json_str(f, (site->types[j].b >= 0) ? class_name(ty, site->types[j].b) : "");
                        fprintf(f, ",%llu]", (unsigned long long)site->types[j].n);
                        tfirst = false;
                }
                fputs("]}", f);
        }

        free(sorted);

        fputs("]}", f);
}

void
jit_slow_sites(JitSlowSiteFn *fn, void *ctx)
{
        for (int i = 0; i < SITE_TABLE_SIZE; ++i) {
                JitSite const *s = &site_table[i];
                i32 classes[SITE_TYPES];
                u64 counts[SITE_TYPES];
                int n = 0;

                if (s->ip == NULL || s->miss == 0) {
                        continue;
                }

                for (int j = 0; j < SITE_TYPES; ++j) {
                        if (s->types[j].n > 0 && s->types[j].a >= 0) {
                                classes[n] = s->types[j].a;
                                counts[n] = s->types[j].n;
                                n += 1;
                        }
                }

                fn(ctx, s->ip, site_kind_names[s->kind], s->miss, classes, counts, n);
        }
}

#define SITE_MISS(kind, a, b) (UNLIKELY(JitStatsOn) ? jit_site_miss(ty, __builtin_return_address(0), (kind), (a), (b)) : (void)0)

#define TOP_OF_STACK(v) (vN(STACK) = ((v) - vv(STACK)) + 1)

void
jit_rt_add(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z + b->z);
                return;
        }

        STAT(arith_slow);
        SITE_MISS(SITE_ARITH, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_ADD, a, b);
        *v_(STACK, idx) = val;
}

void
jit_rt_sub(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z - b->z);
                return;
        }

        STAT(arith_slow);
        SITE_MISS(SITE_ARITH, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_SUB, a, b);
        *v_(STACK, idx) = val;
}

void
jit_rt_mul(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z * b->z);
                return;
        }

        STAT(arith_slow);
        SITE_MISS(SITE_ARITH, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_MUL, a, b);
        *v_(STACK, idx) = val;
}

void
jit_rt_div(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                if (b->z == 0) ZeroDividePanic(ty);
                *result = INTEGER(IntDiv(a->z, b->z));
                return;
        }

        STAT(arith_slow);
        SITE_MISS(SITE_ARITH, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_DIV, a, b);
        *v_(STACK, idx) = val;
}

void
jit_rt_mod(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                if (b->z == 0) ZeroDividePanic(ty);
                *result = INTEGER(IntMod(a->z, b->z));
                return;
        }

        STAT(arith_slow);
        SITE_MISS(SITE_ARITH, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = vm_2op(ty, OP_MOD, a, b);
        *v_(STACK, idx) = val;
}

void
jit_rt_neg(Ty *ty, Value *result, Value *a)
{
        if (a->type == VALUE_INTEGER) {
                *result = INTEGER(-a->z);
                return;
        }

        if (a->type == VALUE_REAL) {
                *result = REAL(-a->real);
                return;
        }

        vN(STACK) = (result - vv(STACK)) + 1;

        vm_jit_neg(ty);
}

void
jit_rt_eq(Ty *ty, Value *result, Value *a, Value *b)
{
        if (LIKELY(a->type == VALUE_NIL || b->type == VALUE_NIL)) {
                *result = BOOLEAN(a->type == b->type);
                return;
        }

        SITE_MISS(SITE_COMPARE, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = BOOLEAN(v_eq(a, b));
        *v_(STACK, idx) = val;
}

void
jit_rt_ne(Ty *ty, Value *result, Value *a, Value *b)
{
        if (LIKELY(a->type == VALUE_NIL || b->type == VALUE_NIL)) {
                *result = BOOLEAN(a->type != b->type);
                return;
        }

        SITE_MISS(SITE_COMPARE, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        Value val = BOOLEAN(!v_eq(a, b));
        *v_(STACK, idx) = val;
}

void
jit_rt_lt(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z < b->z);
                return;
        }

        SITE_MISS(SITE_COMPARE, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        DoLt(ty);
}

void
jit_rt_le(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z <= b->z);
                return;
        }

        SITE_MISS(SITE_COMPARE, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        DoLeq(ty);
}

void
jit_rt_gt(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z > b->z);
                return;
        }

        SITE_MISS(SITE_COMPARE, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        DoGt(ty);
}

void
jit_rt_ge(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z >= b->z);
                return;
        }

        SITE_MISS(SITE_COMPARE, a, b);

        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 2;

        DoGeq(ty);
}

static void
jit_run_trampoline(Ty *ty, JitFn *jit, Value **env);


static bool
jit_rt_getter(Ty *ty, ptrdiff_t idx, Value const *obj, Value const *fn)
{
        if (
                (fn == NULL)
             || (fn->type != VALUE_FUNCTION)
             || (param_count_of(fn) != 0)
             || (rest_idx_of(fn) >= 0)
             || (kwargs_idx_of(fn) >= 0)
             || is_starred(fn)
        ) {
                return false;
        }

        JitFn *jit = try_jit(ty, fn);
        if (jit == NULL) {
                return false;
        }

        Value self = *obj;
        Value callee = *fn;
        vN(STACK) = idx;
        jit_fast_frame(ty, &callee, &self, 0);
        jit_run_trampoline(ty, jit, callee.env);
        return true;
}

void
jit_rt_member(Ty *ty, Value *result, Value *obj, int member_id)
{
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 1;

        if (obj == NULL) {
                obj = vm_get_self(ty);
                v_L(STACK) = *obj;
        }

        SITE_MISS(SITE_MEMBER, obj, NULL);

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
                                if (
                                        (kind == OFF_GETTER)
                                     && jit_rt_getter(ty, idx, obj, v_(cls->getters.values, off & OFF_MASK))
                                ) {
                                        STAT(member_fast);
                                        return;
                                }
                        }
                }
        }

        if (
                (
                        (obj->type == VALUE_REAL)
                     || (obj->type == VALUE_INTEGER)
                     || (obj->type == VALUE_BOOLEAN)
                )
             && jit_rt_getter(ty, idx, obj, class_lookup_getter_i(ty, ClassOf(obj), member_id))
        ) {
                STAT(member_fast);
                return;
        }

        if (obj->type == VALUE_TUPLE && obj->ids != NULL) {
                for (int i = 0; i < obj->count; ++i) {
                        if (obj->ids[i] == member_id) {
                                STAT(member_fast);
                                *result = obj->items[i];
                                return;
                        }
                }
        }

        STAT(member_slow);
        Value value = vm_jit_member_access(ty, member_id);
        vN(STACK) = idx + 1;
        *v_(STACK, idx) = value;
}

void
jit_rt_try_member(Ty *ty, Value *top, int member_id)
{
        vN(STACK) = top - vv(STACK);
        vm_jit_try_member_access(ty, member_id);
}

void
jit_rt_get_member(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        vm_jit_get_member(ty);
}

void
jit_rt_try_get_member(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        vm_jit_try_get_member(ty);
}

int
jit_rt_try_tag_pop(Ty *ty, Value *val, int tag)
{
        return TryUnwrap(val, tag);
}

int
jit_rt_index_tuple(Value *tos, Value *dst, int i)
{
        if (tos->type != VALUE_TUPLE || tos->count <= i) {
                return 0;
        }
        *dst = tos->items[i];
        return 1;
}

int
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

int
jit_rt_try_steal_tag(Ty *ty, Value *tos, Value *target)
{
        if (tos->tags > 0) {
                *target = TAG(tags_first(ty, tos->tags));
                (PopTag)(ty, tos);
                return 1;
        }

        return 0;
}

void
jit_rt_tag_push(Ty *ty, Value *v, int tag)
{
        v->tags = tags_push(ty, v->tags, tag);
        v->type |= VALUE_TAGGED;
}

int
jit_rt_try_regex(Ty *ty, Value *str, Regex *re, Value *top)
{
        vN(STACK) = top - vv(STACK);
        Value regex = REGEX(re);
        xvP(STACK, regex);
        if (str->type == VALUE_STRING) {
                Value result = string_match(ty, str, 1, NULL);
                if (result.type != VALUE_NIL) {
                        *vvL(STACK) = result;
                        return 1;
                }
        }
        vvX(STACK);
        return 0;
}

void
jit_rt_assign_regex_matches(Ty *ty, Value *match, int n)
{
        Value *vp = vm_jit_pop_target(ty);
        if (match->type == VALUE_ARRAY) {
                int i = 0;
                for (; i < vN(*match->array); ++i) {
                        vp[i] = v__(*match->array, i);
                }
                while (i < n + 1) {
                        vp[i++] = NIL;
                }
        } else {
                *vp = *match;
        }
}

int
jit_rt_jii(Ty *ty, Value *v, int class_id)
{
        return class_is_subclass(ty, ClassOf(v), class_id);
}

void
jit_rt_capture(Ty *ty, Value *local, Value **env, int env_idx)
{
        Value *vp = uAo(sizeof (Value), GC_VALUE);
        *vp = *local;
        *local = REF(vp);
        env[env_idx] = vp;
}

i32
jit_rt_match_string(Value const *v, i32 table_size, char const *table)
{
        if (v->type != VALUE_STRING || table_size <= 0) {
                return -1;
        }

        u64 h = XXH3_64bits(ss(*v), sN(*v));
        u32 bucket = (u32)(h & (u32)(table_size - 1));
        for (;;) {
                i32 id;
                memcpy(&id, table + bucket * 2 * sizeof (i32), sizeof id);
                if (id == -1) {
                        return -1;
                }

                InternEntry const *entry = intern_entry(&xD.strings, id);
                u32 len = (u32)(uptr)entry->data;
                if (sN(*v) == len && memcmp(ss(*v), entry->name, len) == 0) {
                        return (i32)bucket;
                }
                bucket = (bucket + 1) & (u32)(table_size - 1);
        }
}

void
jit_rt_function(Ty *ty, Value *top, char const *ip, Value *locals, Value **env)
{
        vN(STACK) = top - vv(STACK);
        (void)DoFunction(ty, ip, locals, env);
}

void
jit_rt_generator(Ty *ty, Value *top, char const *ip, Value *locals, Value **env)
{
        vN(STACK) = top - vv(STACK);
        (void)DoGenerator(ty, ip, locals, env);
}

void
jit_rt_patch_env(Ty *ty, Value *top, int n)
{
        (void)ty;
        *top->env[n] = *top;
}

int
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

void
jit_rt_tuple(Ty *ty, Value *top, i32 n, i32 *ids)
{
        vN(STACK) = top - vv(STACK);

        Value *items = mAo(n * sizeof (Value), GC_TUPLE);
        Value tuple = TUPLE(items, ids, n);

        memcpy(items, vZ(STACK) - n, n * sizeof (Value));
        vN(STACK) -= n;

        xvP(STACK, tuple);
}

void
jit_rt_subscript(Ty *ty, Value *top)
{
        ptrdiff_t idx = (top - vv(STACK));
        vN(STACK) = idx + 2;
        DoSubscript(ty, true);
}

void
jit_rt_safe_subscript(Ty *ty, Value *top)
{
        ptrdiff_t idx = (top - vv(STACK));
        vN(STACK) = idx + 2;
        DoSafeSubscript(ty, true);
}

int
jit_rt_truthy(Ty *ty, Value *v)
{
        return value_truthy(ty, v);
}

void
jit_rt_bit_and(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_AND, true);
}

void
jit_rt_bit_or(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_OR, true);
}

void
jit_rt_bit_xor(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_XOR, true);
}

void
jit_rt_shl(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_SHL, true);
}

void
jit_rt_shr(Ty *ty, Value *result, Value *a, Value *b)
{
        TOP_OF_STACK(a + 1);
        DoBinaryOp(ty, OP_BIT_SHR, true);
}

void
jit_rt_inc(Ty *ty, Value *v)
{
        TOP_OF_STACK(v);
        IncValue(ty, v);
}

void
jit_rt_dec(Ty *ty, Value *v)
{
        TOP_OF_STACK(v);
        DecValue(ty, v);
}

void
jit_rt_string(Ty *ty, Value *result, i32 i)
{
        InternEntry const *interned = intern_entry(&xD.strings, i);
        *result = STRING_NOGC(interned->name, (uptr)interned->data);
}

void
jit_rt_tail_loop(Value *locals, Value const *arguments, int param_count,
                 int bound, int kept)
{
        memmove(locals, arguments, param_count * sizeof *locals);
        for (int i = kept; i < bound; ++i) {
                locals[i] = NIL;
        }
        STAT(self_tail_fast);
}

void
jit_rt_call_global_kw(Ty *ty, Value *top, int gi, int n, int nkw, char *kw_ip)
{
        vN(STACK) = top - vv(STACK);
        Value kwargs = BuildKwargsDict(ty, &kw_ip, nkw);
        DoCallEx(ty, v_(Globals, gi), n, &kwargs, true);
}

void
jit_rt_call_kw(Ty *ty, Value *top, int n, int nkw, char *kw_ip)
{
        vN(STACK) = top - vv(STACK);
        Value f = vXx(STACK);
        Value kwargs = BuildKwargsDict(ty, &kw_ip, nkw);
        DoCallEx(ty, &f, n, &kwargs, true);
}


void
jit_rt_call_method_kw(Ty *ty, Value *top, int z, int n, int nkw, char *kw_ip)
{
        jit_call_method_at(ty, top, z, n, nkw, kw_ip, false);
}

void
jit_rt_cmp(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + 2;
        DoCmp(ty);
}

void
jit_rt_count(Ty *ty, Value *result, Value *v)
{
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + 1;
        DoCount(ty, true);
}

void
jit_rt_assign_subscript(Ty *ty, Value *top, int n)
{
        vN(STACK) = top - vv(STACK);
        DoAssignSubscript(ty, n, true);
}

void
jit_rt_array(Ty *ty, Value *result, Value *elements, int n)
{
        ptrdiff_t idx = result - vv(STACK);
        vN(STACK) = idx + n;

        Array *xs = vAn(n);
        vN(*xs) = n;

        memcpy(vv(*xs), v_(STACK, idx), n * sizeof (Value));

        *v_(STACK, idx) = ARRAY(xs);
}

void
jit_rt_array0(Ty *ty, Value *result)
{
        *result = ARRAY(uAo0(sizeof (Array), GC_ARRAY));
}

void
jit_rt_array_compr(Ty *ty, Value *top, i32 idx, i32 n)
{
        vN(STACK) = top - vv(STACK);
        Value *array = vZ(STACK) - (idx + n + 1);
        vvPn(*array->array, vZ(STACK) - n, n);
        vN(STACK) -= n;
}

void
jit_rt_loop_iter(Ty *ty, Value *top)
{
        TOP_OF_STACK(top - 1);
        vm_jit_loop_iter(ty);
}

int
jit_rt_loop_check(Ty *ty, int z, Value *top)
{
        TOP_OF_STACK(top);
        return vm_jit_loop_check(ty, z);
}

void
jit_rt_throw(Ty *ty, Value *exc)
{
        ptrdiff_t idx = (exc - vv(STACK));
        vN(STACK) = idx + 1;
        vm_throw(ty, exc);
}

void
jit_rt_range(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + 2;
        Value val = vm_make_range(ty, a, b, false);
        *v_(STACK, idx) = val;
}

void
jit_rt_incrange(Ty *ty, Value *result, Value *a, Value *b)
{
        ptrdiff_t idx = (result - vv(STACK));
        vN(STACK) = idx + 2;
        Value val = vm_make_range(ty, a, b, true);
        *v_(STACK, idx) = val;
}

void
jit_rt_catch(Ty *ty)
{
        vXx(ty->throw_stack);
        v_L(ty->st->try_stack)->state = TRY_FINALLY;
}

void
jit_rt_rethrow_setup(Ty *ty)
{
        struct try *t = ty->st->try_stack.items[ty->st->try_stack.count - 1];
        t->state = TRY_THROW;
        t->end = NULL;
}

void
jit_rt_finally_enter(Ty *ty, char *resume_addr)
{
        struct try *t = ty->st->try_stack.items[ty->st->try_stack.count - 1];
        t->state = TRY_FINALLY;
        t->end = resume_addr;
}

char *
jit_rt_end_try(Ty *ty)
{
        return vXx(ty->st->try_stack)->end;
}

void
jit_rt_pop_try(Ty *ty)
{
        if (vXx(ty->st->try_stack)->end == NULL) {
                vXx(ty->throw_stack);
        }
}

int
jit_rt_tuple_rest(Ty *ty, Value *tos, i32 start)
{
        Value *target = vm_jit_pop_target(ty);
        return vm_jit_tuple_rest(ty, tos, target, start) ? 1 : 0;
}

static int JitAudit = -1;

int
jit_audit_level(void)
{
        if (JitAudit < 0) {
                char const *s = getenv("TY_JIT_AUDIT");
                JitAudit = (s == NULL || *s == '\0') ? 0 : atoi(s);
                if (JitAudit <= 0 && s != NULL && *s != '\0') {
                        JitAudit = 1;
                }
        }

        return JitAudit;
}

int
jit_rt_call_trampoline(Ty *ty, Value *out, Value *fn, int argc)
{
        Value _fn = *fn;

        vN(STACK) = (out + argc) - vv(STACK);

        JitFn *jit;

        if (
                (_fn.type != VALUE_FUNCTION && _fn.type != VALUE_BOUND_FUNCTION)
             || is_starred(&_fn)
             || ((jit = try_jit(ty, &_fn)) == NULL)
        ) {
                DoCallEx(ty, &_fn, argc, &NIL, true);
                return 0;
        }

        vm_xcall(ty, &_fn, NULL, argc, NULL);

        vvL(ty->st->frames)->f.type = VALUE_NATIVE_FUNCTION;
        vvL(ty->st->frames)->f.tags = 0;

        ty->ip = &JIT;

        return 1;
}


static inline void
jit_run_trampoline(Ty *ty, JitFn *jit, Value **env)
{
        CO_LOG("jit_run_trampoline", TERM(32;1), "enter");

        vm_trampoline_linked(ty, jit, env);

        CO_LOG("jit_run_trampoline", TERM(31;1), "ret");
}

static bool
jit_baked_method_live(Ty *ty, int class_id, int member_id, Value const *baked)
{
        if (LIKELY(atomic_load_explicit(&ClassMethodEpoch, memory_order_acquire) == 0)) {
                return true;
        }

        Class *c = class_get(ty, class_id);

        if (member_id >= vN(c->offsets_r)) {
                return false;
        }

        u16 off = v__(c->offsets_r, member_id);

        if ((off >> OFF_SHIFT) != OFF_METHOD) {
                return false;
        }

        Value const *live = v_(c->methods.values, off & OFF_MASK);

        return live->type == VALUE_FUNCTION
            && live->info == baked->info
            && live->env == baked->env;
}

static int
jit_rt_baked_call(Ty *ty, Value *self, Value *fn, int64_t class_and_member, int argc)
{
        int class_id  = (int)(class_and_member >> 32);
        int member_id = (int)(class_and_member);

        if (UNLIKELY(ClassOf(self) != class_id)) {
                return 0;
        }

        if (UNLIKELY(!jit_baked_method_live(ty, class_id, member_id, fn))) {
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
        jit_run_trampoline(ty, jit, fn->env);

        return 1 + (items != vv(ty->st->stack));
}

static bool
jit_linkable_function(Value const *fn, int argc)
{
        return fn->type == VALUE_FUNCTION
            && (argc == param_count_of(fn))
            && (rest_idx_of(fn) == -1)
            && (kwargs_idx_of(fn) == -1)
            && !is_starred(fn)
            && !is_overload(fn);
}

bool
jit_linkable_global(Value const *fn, int argc)
{
        return jit_linkable_function(fn, argc) && class_of(fn) == -1;
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
        CallMethod(ty, member_id, argc, 0, false, true);
        CO_LOG("jit_rt_call", TERM(32;1), "");
}

void
jit_rt_call_builtin_method(Ty *ty, Value *result, Value *self,
                           BuiltinMethod *func, int64_t vtype_and_member, int argc)
{
        int value_type = (int)(vtype_and_member >> 32);
        int member_id  = (int)(vtype_and_member);

        if (self == NULL) {
                self = vm_get_self(ty);
        }

        Value _self = *self;

        CO_LOG("jit_rt_call_builtin_method", TERM(32;1), "type %d member %d", value_type, member_id);

        if (LIKELY(self->type == value_type)) {
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
                SITE_MISS(SITE_METHOD, &_self, NULL);
                jit_rt_call_method(ty, result, &_self, member_id, argc);
        }
}

int
jit_rt_yield(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        DoYield(ty);
        CheckInterrupt(ty);
        return vvL(ty->st->frames)->fp;
}

int
jit_rt_yield_some(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        v_L(STACK) = Some(v_L(STACK));
        DoYield(ty);
        CheckInterrupt(ty);
        return vvL(ty->st->frames)->fp;
}

int
jit_rt_yield_none(Ty *ty, Value *top)
{
        vN(STACK) = top - vv(STACK);
        if (vN(ty->st->frames) > 1) {
                xvP(STACK, NIL);
                return -1;
        }
        xvP(STACK, None);
        DoYield(ty);
        CheckInterrupt(ty);
        return vvL(ty->st->frames)->fp;
}

void
jit_rt_check_match(Ty *ty, Value *result, Value *value, Value *pattern)
{
        vN(STACK) = result - vv(STACK) + 2;
        DoCheckMatch(ty, true);
}

void
jit_rt_concat_strings(Ty *ty, Value *result, Value *base, int n)
{
        ptrdiff_t result_idx = result - vv(STACK);

        vN(STACK) = (base - vv(STACK)) + n;
        vm_concat_strings(ty, n);

        *v_(STACK, result_idx) = *vvL(STACK);
}

Class *
expected_class_of(Ty *ty, T2Type t)
{
        return t2_class_of(ty, t);
}

T2Type
find_type_hint(TypeHintVector const *hints, iptr off)
{
        isize lo = 0;
        isize hi = vN(*hints) - 1;

        while (lo <= hi) {
                isize m = (lo + hi) / 2;
                TypeHint *hint = v_(*hints, m);
                if (hint->pc == off) {
                        while (m + 1 < vN(*hints) && v_(*hints, m + 1)->pc == off) {
                                m += 1;
                        }
                        return v_(*hints, m)->type;
                } else if (hint->pc < off) {
                        lo = m + 1;
                } else {
                        hi = m - 1;
                }
        }

        return T2_TYPE_INVALID;
}


BuiltinMethod *
jit_builtin_method(Class *cls, int member_id, int *value_type)
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

        case CLASS_SET:
                func = get_set_method_i(member_id);
                vtype = VALUE_SET;
                break;

        case CLASS_BLOB:
                func = get_blob_method_i(member_id);
                vtype = VALUE_BLOB;
                break;

        case CLASS_QUEUE:
                func = get_queue_method_i(member_id);
                vtype = VALUE_QUEUE;
                break;

        case CLASS_HEAP:
                func = get_heap_method_i(member_id);
                vtype = VALUE_HEAP;
                break;

        case CLASS_SHARED_QUEUE:
        case CLASS_WORK_QUEUE:
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


int
jit_tier(void)
{
        static int tier = -1;
        if (tier < 0) {
                char const *s = getenv("TY_JIT_TIER");
                tier = s == NULL ? 0 : atoi(s);
        }
        return tier;
}

JitFn *
jit_promote(Ty *ty, Value const *f)
{
        _Atomic i16 *flags   = (void *)flags_of(f);
        i16          flags0  = atomic_load(flags);
        void        *current = jit_of(f);

        if (current == NULL || jit_pending(current)) {
                return NULL;
        }

        if (
                (flags0 & FF_JIT_TIER2)
             || DebugJitOff
             || !atomic_compare_exchange_strong(flags, &flags0, flags0 | FF_JIT_TIER2)
        ) {
                return current;
        }

        JitFn *next = jit_compile(ty, f);

        if (next == NULL) {
                return current;
        }

        set_jit_of(f, next);

        return next;
}

JitFn *
jit_despecialize(Ty *ty, Value const *f)
{
        _Atomic i16 *flags  = (void *)flags_of(f);
        i16          flags0 = atomic_load(flags);

        if (
                (flags0 & FF_JIT_NOSPEC)
             || DebugJitOff
             || !atomic_compare_exchange_strong(flags, &flags0, flags0 | FF_JIT_NOSPEC)
        ) {
                return NULL;
        }

        JitFn *next = jit_compile(ty, f);

        if (next != NULL) {
                set_jit_of(f, next);
        }

        return next;
}

int
jit_eager(void)
{
        static int eager = -1;
        if (eager < 0) {
                char const *s = getenv("TY_JIT_EAGER");
                eager = (s == NULL || *s == '\0') ? 0 : atoi(s) == 2 ? 2 : 1;
        }
        return eager;
}

bool
jit_hot_on_entry(Value const *f)
{
        return jit_eager() == 1;
}

bool
jit_pinned_loop(Value const *f)
{
        char const *code = code_of(f);
        char const *end = code + code_size_of(f);
        bool loop = false;
        bool pinned = false;
        for (char const *ip = code; ip < end; ip = StepInstruction(ip)) {
                switch ((u8)*ip) {
                case INSTR_JUMP: {
                        i32 jump;
                        memcpy(&jump, ip + 1, sizeof jump);
                        loop = loop || jump < 0;
                        break;
                }
                case INSTR_TRY:
                case INSTR_SPREAD_CHECK:
                case INSTR_TRY_YIELD_FROM:
                        pinned = true;
                        break;
                default:
                        break;
                }
        }
        return loop && pinned;
}

JitFn *
jit_compile(Ty *ty, Value const *func)
{
        return jit_lower(ty, func);
}

void
jit_init(Ty *ty)
{
        (void)ty;
        lir_set_runtime(&LirVM);
        TySpinLockInit(&JitLogMutex);
}

void
jit_free(Ty *ty)
{
        (void)ty;
        jm_trim();
}
