static bool
bc_cache_plan(BcLir *c, Ty *ty, Value const *f)
{
        if (getenv("TY_JIT_REGISTERIZE") == NULL || c->bound == 0) {
                return true;
        }
        Expr const *expr = expr_of(f);
        if (expr == NULL || expr->scope == NULL) {
                return true;
        }
        i32 *weights = calloc((usize)c->size + 1, sizeof *weights);
        u32 *scores = calloc(c->bound, sizeof *scores);
        c->cached = calloc(c->bound, sizeof *c->cached);
        c->cache_at = malloc(c->bound * sizeof *c->cache_at);
        if (weights == NULL || scores == NULL || c->cached == NULL || c->cache_at == NULL) {
                free(weights);
                free(scores);
                return false;
        }
        for (i32 slot = 0; slot < c->bound; ++slot) {
                c->cache_at[slot] = -1;
        }
        for (i32 off = 0; off < c->size;) {
                BcLirNode const *node = &c->nodes[off];
                if (node->sp >= 0 && node->branch && node->target <= off) {
                        weights[node->target] += 16;
                        weights[off + 1] -= 16;
                }
                off = node->next;
        }
        i32 weight = 0;
        for (i32 off = 0; off < c->size; ++off) {
                weight += weights[off];
                BcLirNode const *node = &c->nodes[off];
                if (node->next == 0 || node->sp < 0 || weight == 0) {
                        continue;
                }
                if (node->op == INSTR_LOAD_LOCAL || node->op == INSTR_ASSIGN_LOCAL
                    || node->op == INSTR_TARGET_LOCAL) {
                        i32 slot;
                        memcpy(&slot, c->code + off + 1, sizeof slot);
                        if (slot >= 0 && slot < c->bound) {
                                scores[slot] += weight;
                        }
                }
        }
        for (i32 slot = 0; slot < c->bound && slot < vN(expr->scope->owned); ++slot) {
                Symbol *symbol = v__(expr->scope->owned, slot);
                if (scores[slot] == 0 || slot == c->self_index || SymbolIsCaptured(symbol)) {
                        continue;
                }
                Class *class = expected_class_of(ty, symbol->type);
                if (class == NULL || (class->i != CLASS_INT && class->i != CLASS_FLOAT)) {
                        continue;
                }
                BcLocal *local = &c->cached[c->ncached];
                c->cache_at[slot] = c->ncached++;
                local->slot = slot;
                local->floating = class->i == CLASS_FLOAT;
                for (u32 i = 0; i < countof(local->regs); ++i) {
                        local->regs[i] = lir_reg(c->L, i == 1 && local->floating ? LIR_F64 : LIR_I64);
                }
        }
        free(weights);
        free(scores);
        return true;
}

static void
bc_cached_store(BcLir *c, BcLocal const *local, LirReg base, i32 offset)
{
        for (u32 i = 0; i < countof(local->regs); ++i) {
                LirOp op = i == 1 && local->floating ? LIR_ST_F64 : LIR_ST64;
                bc_store(c, op, base, offset + i * 8, lir_r(local->regs[i]));
        }
}

static void
bc_cached_load(BcLir *c, BcLocal const *local, LirReg base, i32 offset)
{
        for (u32 i = 0; i < countof(local->regs); ++i) {
                LirOp op = i == 1 && local->floating ? LIR_LD_F64 : LIR_LD_I64;
                LirOpnd memory = lir_m(base, LIR_NONE, 1, offset + i * 8);
                c->ok = c->ok && lir_emit_to(c->L, op, local->regs[i], &memory, 1);
        }
}

static void
bc_cache_flush(BcLir *c)
{
        if (!c->cache_ready) {
                return;
        }
        for (u32 i = 0; i < c->ncached; ++i) {
                BcLocal const *local = &c->cached[i];
                bc_cached_store(c, local, c->locals, local->slot * sizeof (Value));
        }
}

static void
bc_cache_reload(BcLir *c)
{
        for (u32 i = 0; i < c->ncached; ++i) {
                BcLocal const *local = &c->cached[i];
                bc_cached_load(c, local, c->locals, local->slot * sizeof (Value));
        }
        c->cache_ready = true;
}

static void
bc_local_load(BcLir *c, i32 slot)
{
        i32 cached = c->cache_at == NULL ? -1 : c->cache_at[slot];
        if (cached < 0) {
                bc_value_copy(c, c->ops, c->sp++ * sizeof (Value), c->locals, slot * sizeof (Value));
                return;
        }
        bc_cached_store(c, &c->cached[cached], c->ops, c->sp++ * sizeof (Value));
}

static void
bc_local_store(BcLir *c, i32 slot)
{
        i32 cached = c->cache_at == NULL ? -1 : c->cache_at[slot];
        if (cached < 0) {
                bc_value_copy(c, c->locals, slot * sizeof (Value), c->ops, --c->sp * sizeof (Value));
                return;
        }
        bc_cached_load(c, &c->cached[cached], c->ops, --c->sp * sizeof (Value));
}
