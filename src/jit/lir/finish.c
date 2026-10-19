#include <regex.h>
#include <stdatomic.h>

#include "ty.h"
#include "jit/lir.h"

typedef struct {
        bool entry;
        bool interpreted;
        bool thunk;
        bool owned;
        u32  slots;
} Plan;

static LirCode *
compile(Ty *ty, Lir *L, Plan p, LirError *err);

static void
trace(Lir const *L, LirAlloc const *alloc, char const *stage)
{
        char const *pattern = getenv("TY_JIT_DUMP");
        regex_t     re;

        if (
                (pattern == NULL)
             || (*pattern == '\0')
             || (regcomp(&re, pattern, REG_EXTENDED | REG_NOSUB) != 0)
        ) {
                return;
        }

        bool hit = regexec(&re, L->name, 0, NULL, 0) == 0;

        regfree(&re);

        if (!hit) {
                return;
        }

        flockfile(stderr);
        fprintf(stderr, "jit-dump: %s stage=%s\n", L->name, stage);
        lir_dump(L, stderr);

        if (alloc != NULL) {
                fprintf(
                        stderr,
                        "frame: %u bytes, %u vslots\n",
                        alloc->frame_size,
                        alloc->nvslots
                );
                lir_dump_alloc(L, alloc, stderr);
        }

        funlockfile(stderr);
}

static _Atomic u64 Serial;

static LirCode *
shell(Lir *L, Plan p, LirError *err)
{
        LirCode *code = xtA0(LirCode, 1);

        code->serial = atomic_fetch_add(&Serial, 1) + 1;

        code->entry_thunk      = p.thunk;
        code->entry_body_slots = p.slots;
        code->name             = S2(L->name);
        code->mode             = L->resolved_mode;
        code->release          = (L->mode == LIR_MODE_DETACHED);
        code->nroots           = vN(L->roots);
        code->roots            = xtA0(Value, vN(L->roots) + 1);

        for (u32 i = 0; i < vN(L->roots); ++i) {
                code->roots[i] = v__(L->roots, i);
        }

        if (p.owned) {
                code->sig         = L->sig;
                code->sig.params  = NULL;
                code->sig.nparams = 0;
                code->sig.nfixed  = 0;
                return code;
        }

        code->lir = lir_clone(L, err);

        if (code->lir == NULL) {
                lir_code_free(code);
                return NULL;
        }

        code->sig = code->lir->sig;

        return code;
}

static bool
interpret(LirCode *code, Lir const *L, LirError *err)
{
        if (!lir_interp_emit(code, err)) {
                return false;
        }

        code->nvslots = L->nvslots;

        return true;
}

static bool
native(Ty *ty, Lir *L, LirCode *code, bool owned, LirTarget const *target, LirError *err)
{
        Lir           *legal = owned ? L : lir_clone(L, err);
        LirCFG         cfg   = {0};
        LirAlloc       alloc = {0};
        LirConstraint *cs    = NULL;
        u32            ncs   = 0;

        SCRATCH_SAVE();

        bool ok = (legal != NULL)
               && lir_optimize(ty, legal)
               && lir_legalize(ty, legal, target, &cs, &ncs, err)
               && lir_cfg(ty, legal, &cfg, err)
               && lir_allocate(ty, legal, &cfg, target, cs, ncs, &alloc, err);

        if (ok) {
                code->nvslots = alloc.nvslots;
                trace(legal, NULL, "legal");
                trace(legal, &alloc, "alloc");
                ok = target->emit(ty, legal, &alloc, code, err);
        }

        SCRATCH_RESTORE();

        if (legal != L) {
                lir_free(legal);
        }

        return ok;
}

static bool
reserve(Lir *thunk, u64 slots)
{
        uptr fn = (uptr)lir_runtime()->reserve;

        for (u32 pc = 0; pc < vN(thunk->insts); ++pc) {
                LirInst *in = v_(thunk->insts, pc);
                if (
                        (in->op == LIR_CALL)
                     && (in->args[0].kind == LO_IMM)
                     && ((uptr)in->args[0].imm == fn)
                ) {
                        in->call_args[2] = lir_i(slots);
                        return true;
                }
        }

        return false;
}

static bool
attach(Ty *ty, LirCode *code, bool interpreted, LirError *err)
{
        LirCode shadow = *code;

        if (interpreted || lir_target() == NULL) {
                shadow.nvslots = 0;
        }

        Lir *thunk = lir_build_entry(ty, &shadow, err);

        if (thunk == NULL) {
                return false;
        }

        Plan p = { .interpreted = interpreted, .thunk = true, .slots = code->nvslots };

        code->entry_code = compile(ty, thunk, p, err);

        if (code->entry_code != NULL && code->entry_code->nvslots != 0) {
                if (!reserve(thunk, (u64)code->nvslots + code->entry_code->nvslots)) {
                        lir_free(thunk);
                        return lir_fail(
                                err,
                                LE_MODE,
                                LIR_NOWHERE,
                                "entry thunk needs value slots"
                        );
                }
                lir_code_free(code->entry_code);
                code->entry_code = compile(ty, thunk, p, err);
        }

        lir_free(thunk);

        if (code->entry_code == NULL) {
                return false;
        }

        code->entry = code->entry_code->body;

        return true;
}

static LirCode *
compile(Ty *ty, Lir *L, Plan p, LirError *err)
{
        LirTarget const *target   = lir_target();
        bool             paranoid = getenv("TY_JIT_VALIDATE") != NULL;
        bool             check    = !p.thunk && (!p.owned || paranoid);

        if (err != NULL) {
                *err = (LirError) {0};
        }

        if (check && !lir_validate(ty, L, err)) {
                return NULL;
        }

        if (p.owned && !lir_prepare(ty, L, err)) {
                return NULL;
        }

        trace(L, NULL, "lir");

        LirCode *code = shell(L, p, err);
        bool     ok   = (code != NULL);

        if (ok && (p.interpreted || target == NULL)) {
                ok = interpret(code, L, err);
        } else if (ok) {
                ok = native(ty, L, code, p.owned, target, err);
        }

        if (ok && p.entry) {
                ok = attach(ty, code, p.interpreted, err);
        }

        if (ok) {
                return code;
        }

        lir_code_free(code);

        if (err != NULL && err->kind == LE_NONE) {
                lir_fail(err, LE_TARGET, LIR_NOWHERE, "could not compile LIR");
        }

        return NULL;
}

LirCode *
lir_finish(Ty *ty, Lir *L, bool entry, LirError *err)
{
        return compile(ty, L, (Plan) { .entry = entry }, err);
}

LirCode *
lir_finish_owned(Ty *ty, Lir *L, LirError *err)
{
        return compile(ty, L, (Plan) { .owned = true }, err);
}

LirCode *
lir_finish_interpreted(Ty *ty, Lir *L, bool entry, LirError *err)
{
        return compile(ty, L, (Plan) { .entry = entry, .interpreted = true }, err);
}

void
lir_code_destroy(LirCode *code)
{
        if (code == NULL) {
                return;
        }

        jm_free(code->allocation);
        lir_interp_destroy(code);
        lir_code_free(code->entry_code);
        lir_free(code->lir);
        xmF(code->roots);
        xmF(code->sites);
        xmF(code->marks);
        xmF(code->entries);
        xmF(code->name);
        xmF(code->osr);
        xmF(code->tier);
}

void
lir_code_free(LirCode *code)
{
        lir_code_destroy(code);
        xmF(code);
}
