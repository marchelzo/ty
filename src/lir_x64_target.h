static bool
native_legalize(Lir *L, LirConstraint **out, u32 *nout, LirError *err)
{
        u32 capacity = L->ninsts / 4 + 64;
        LirConstraint *cs = malloc(capacity * sizeof *cs);
        u32 n = 0;
        if (cs == NULL) {
                return emit_error(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory legalizing x64");
        }
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirInst const *in = &L->insts[pc];
                u64 gp = 0;
                u64 fr = 0;
                if (n + 40 > capacity) {
                        LirConstraint *grown = realloc(cs, capacity * 2 * sizeof *cs);
                        if (grown == NULL) {
                                free(cs);
                                return emit_error(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory legalizing x64");
                        }
                        cs = grown;
                        capacity *= 2;
                }
                switch (in->op) {
                case LIR_SDIV:
                case LIR_UDIV:
                case LIR_SREM:
                case LIR_UREM:
                case LIR_MULHS:
                case LIR_MULHU:
                        gp = 5;
                        break;
                case LIR_SHL:
                case LIR_SHR:
                case LIR_SAR:
                case LIR_ROTR:
                        gp = in->args[1].kind == LIR_OPERAND_IMM ? 0 : 2;
                        break;
                case LIR_FMA:
                case LIR_FMIN:
                case LIR_FMAX:
                        gp = 0xfc7;
                        fr = 0x3fff;
                        for (u32 i = 0; i < in->nargs; ++i) {
                                cs[n++] = (LirConstraint) {
                                        .op = pc, .reg = in->args[i].reg, .phys = i,
                                        .fpr = true, .tied = LIR_NONE
                                };
                        }
                        cs[n++] = (LirConstraint) {
                                .op = pc, .reg = in->dst, .phys = 0,
                                .output = true, .fpr = true, .tied = LIR_NONE
                        };
                        break;
                case LIR_CAS:
                        cs[n++] = (LirConstraint) {
                                .op = pc, .reg = in->args[2].reg, .phys = 10,
                                .tied = LIR_NONE
                        };
                        cs[n++] = (LirConstraint) {
                                .op = pc, .reg = in->args[0].mem.base, .phys = 11,
                                .tied = LIR_NONE
                        };
                        cs[n++] = (LirConstraint) {
                                .op = pc, .reg = in->args[1].reg, .phys = 0,
                                .tied = LIR_NONE
                        };
                        cs[n++] = (LirConstraint) {
                                .op = pc, .reg = in->dst, .phys = 0,
                                .output = true, .tied = LIR_NONE
                        };
                        break;
                default:
                        break;
                }
                for (u32 r = 0; r < 16 && ((gp | fr) >> r) != 0; ++r) {
                        if ((gp >> r) & 1) {
                                cs[n++] = (LirConstraint) {
                                        .op = pc, .reg = LIR_NONE, .phys = r,
                                        .output = true, .tied = LIR_NONE
                                };
                        }
                        if ((fr >> r) & 1) {
                                cs[n++] = (LirConstraint) {
                                        .op = pc, .reg = LIR_NONE, .phys = r,
                                        .output = true, .fpr = true, .tied = LIR_NONE
                                };
                        }
                }
        }
        *out = cs;
        *nout = n;
        return true;
}

static LirTarget const NativeTarget = {
        .arch = LIR_ARCH_X64, .abi = LIR_ABI_SYSV, .name = "x64",
        .gpr = { .available = 0xf3cf, .callee_saved = 0xf008,
                 .args = {7, 6, 2, 1, 8, 9}, .nargs = 6, .ret = 0,
                 .scratch = {10, 11}, .nscratch = 2 },
        .fpr = { .available = 0x3fff, .args = {0, 1, 2, 3, 4, 5, 6, 7},
                 .nargs = 8, .ret = 0 },
        .pins = {3, 12, 13, 14, 15}, .npins = 5, .stack_align = 16,
        .legalize = native_legalize, .emit = native_emit
};
