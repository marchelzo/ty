#define LIR_NATIVE
#define main native_scalar_main
#include "lir_interp.c"
#undef main

static void
check_immediates(void)
{
        i64 values[] = {
                INT64_MIN, INT64_MAX, -16773120, -4096, -4095, -1,
                0, 1, 4095, 4096, 16773120, 16773121
        };
        for (u32 width = 0; width < 2; ++width) {
                LirType type = width ? LIR_TYPE_I64 : LIR_TYPE_I32;
                for (u32 op = LIR_ADD; op <= LIR_SUB; ++op) {
                        for (u32 i = 0; i < countof(values); ++i) {
                                Lir *L = function(type, &type, 1);
                                LirReg a = L->params[0];
                                if (!width) {
                                        a = lir_reg(L, LIR_I32);
                                        emit(L, LIR_ZEXT32, a, (LirOpnd[]) { lir_r(L->params[0]) }, 1);
                                }
                                LirReg d = lir_reg(L, width ? LIR_I64 : LIR_I32);
                                emit(L, op, d, (LirOpnd[]) { lir_r(a), lir_i(values[i]) }, 2);
                                ret(L, lir_r(d));
                                LirScalar arg = { .u = width ? 0x7ffffffffffffff8 : 0x7ffffff8 };
                                LirScalar expected = {0};
                                LirError err;
                                CHECK(lir_interpret(NULL, L, &arg, 1, &expected, &err));
                                CHECK(execute(NULL, L, &arg, 1).u == expected.u);
                                lir_free(L);
                        }
                }
        }
}

static void
check_native_pressure(void)
{
        LirType types[48];
        LirScalar args[48];
        for (u32 f = 0; f < 2; ++f) {
                for (u32 i = 0; i < countof(types); ++i) {
                        types[i] = f ? LIR_TYPE_F64 : LIR_TYPE_I64;
                        args[i] = f ? (LirScalar) { .f64 = i + 0.25 } : (LirScalar) { .i = i };
                }
                Lir *L = function(types[0], types, countof(types));
                LirReg acc = lir_reg(L, f ? LIR_F64 : LIR_I64);
                LirOpnd init = f ? lir_f(0.0) : lir_i(0);
                emit(L, f ? LIR_FLI : LIR_LI, acc, &init, 1);
                for (u32 i = 0; i < countof(types); ++i) {
                        emit(L, f ? LIR_FADD : LIR_ADD, acc,
                             (LirOpnd[]) { lir_r(acc), lir_r(L->params[i]) }, 2);
                }
                ret(L, lir_r(acc));
                LirScalar expected = {0};
                LirError err;
                CHECK(lir_interpret(NULL, L, args, countof(args), &expected, &err));
                LirScalar actual = execute(NULL, L, args, countof(args));
                CHECK(actual.u == expected.u);
                lir_free(L);
        }
}

static void
check_spilled_branches(void)
{
        LirType types[48];
        LirScalar args[48];
        for (u32 i = 0; i < countof(types); ++i) {
                types[i] = LIR_TYPE_I64;
                args[i].u = i % 3;
        }
        Lir *L = function(LIR_TYPE_I64, types, countof(types));
        LirReg acc = lir_reg(L, LIR_I64);
        emit(L, LIR_LI, acc, (LirOpnd[]) { lir_i(0) }, 1);
        for (u32 i = 0; i < countof(types); ++i) {
                LirLabel next = lir_label(L);
                emit(L, LIR_BRZ, LIR_NONE, (LirOpnd[]) { lir_r(L->params[i]), lir_l(next) }, 2);
                emit(L, LIR_ADD, acc, (LirOpnd[]) { lir_r(acc), lir_i(1) }, 2);
                CHECK(lir_bind(L, next));
                LirLabel selected = lir_label(L);
                LirLabel fallback = lir_label(L);
                LirLabel end = lir_label(L);
                LirInst in = {
                        .op = LIR_SWITCH, .dst = LIR_NONE,
                        .args = { lir_r(L->params[i]), lir_l(fallback) }, .nargs = 2,
                        .targets = &selected, .ntargets = 1
                };
                CHECK(lir_emit(L, &in));
                CHECK(lir_bind(L, selected));
                emit(L, LIR_ADD, acc, (LirOpnd[]) { lir_r(acc), lir_i(3) }, 2);
                emit(L, LIR_JMP, LIR_NONE, (LirOpnd[]) { lir_l(end) }, 1);
                CHECK(lir_bind(L, fallback));
                emit(L, LIR_ADD, acc, (LirOpnd[]) { lir_r(acc), lir_i(7) }, 2);
                CHECK(lir_bind(L, end));
        }
        for (u32 i = 0; i < countof(types); ++i) {
                emit(L, LIR_ADD, acc, (LirOpnd[]) { lir_r(acc), lir_r(L->params[i]) }, 2);
        }
        ret(L, lir_r(acc));
        LirScalar expected = {0};
        LirError err;
        CHECK(lir_interpret(NULL, L, args, countof(args), &expected, &err));
        CHECK(execute(NULL, L, args, countof(args)).u == expected.u);
        lir_free(L);
}

static void
check_native_entry(void)
{
        LirType types[] = { LIR_TYPE_I64, LIR_TYPE_I64 };
        Lir *L = function(LIR_TYPE_I64, types, 2);
        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
        LirLabel entry = lir_label(L);
        emit(L, LIR_BRNZ, LIR_NONE, (LirOpnd[]) { lir_r(L->params[1]), lir_l(entry) }, 2);
        ret(L, lir_i(7));
        CHECK(lir_entry(L, entry));
        ret(L, lir_r(lir_pinned(L, LIR_PIN_0)));
        CHECK(execute(NULL, L, (LirScalar[]) { { .i = 99 }, { .i = 0 } }, 2).i == 7);
        CHECK(execute(NULL, L, (LirScalar[]) { { .i = 99 }, { .i = 1 } }, 2).i == 99);
        LirError err;
        LirCode *code = lir_finish(L, false, &err);
        CHECK(code != NULL);
        if (code != NULL) {
                CHECK(code->nentries == 1 && code->entries[0].label == entry);
                CHECK(code->entries[0].offset < code->size);
                lir_code_free(code);
        }
        lir_free(L);
}

static u64
site_probe(uptr const **pc)
{
        return **pc;
}

static void
check_tail_loop(void)
{
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I64 };
        Lir *L = function(LIR_TYPE_I64, types, countof(types));
        LirLabel end = lir_label(L);
        emit(L, LIR_BRZ, LIR_NONE, (LirOpnd[]) { lir_r(L->params[1]), lir_l(end) }, 2);
        emit(L, LIR_SUB, L->params[1], (LirOpnd[]) { lir_r(L->params[1]), lir_i(1) }, 2);
        LirOpnd args[] = { lir_r(L->params[0]), lir_r(L->params[1]) };
        LirInst call = {
                .op = LIR_TAILCALL, .dst = LIR_NONE,
                .args = { lir_r(L->params[0]) }, .nargs = 1,
                .sig = L->sig, .call_args = args, .ncall_args = countof(args)
        };
        CHECK(lir_emit(L, &call));
        CHECK(lir_bind(L, end));
        ret(L, lir_i(0));
        LirError err;
        LirCode *code = lir_finish(L, false, &err);
        CHECK(code != NULL);
        if (code != NULL) {
                i64 (*body)(void *, i64) = code->body;
                CHECK(body(code->body, 1000000) == 0);
                lir_code_free(code);
        }
        lir_free(L);
}

static void
check_sites(void)
{
        LirType type = LIR_TYPE_PTR;
        Lir *L = function(LIR_TYPE_U64, &type, 1);
        CHECK(lir_pc_param(L, 0));
        LirReg frame = lir_reg(L, LIR_PTR);
        emit(L, LIR_ALLOCA, frame, (LirOpnd[]) { lir_i(65536), lir_i(16) }, 2);
        emit(L, LIR_SITE, LIR_NONE, (LirOpnd[]) { lir_i(13) }, 1);
        LirReg d = lir_reg(L, LIR_I64);
        LirOpnd args[] = { lir_r(L->params[0]) };
        LirInst call = {
                .op = LIR_CALL, .dst = d,
                .args = { lir_i((uptr)site_probe) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_U64, .params = &type, .nparams = 1, .nfixed = 1 },
                .flags = LIR_CALL_SITE | LIR_RETURNS_TWICE, .tag = 37,
                .call_args = args, .ncall_args = 1
        };
        CHECK(lir_emit(L, &call));
        ret(L, lir_r(d));
        LirError err;
        LirCode *code = lir_finish(L, false, &err);
        CHECK(code != NULL);
        if (code != NULL) {
                uptr const *pc = NULL;
                u64 (*body)(uptr const **) = code->body;
                u64 address = body(&pc);
                CHECK(code->nsites == 2);
                CHECK(address - (uptr)code->body == code->sites[1].pc);
                CHECK(code->sites[0].tag == 13 && code->sites[1].tag == 37);
                LirImage const *header = (LirImage *)code->body - 1;
                LirSite const *sites = (void *)((u8 *)code->body + header->table);
                CHECK(header->size == code->size && header->nsites == code->nsites);
                CHECK(memcmp(sites, code->sites, code->nsites * sizeof *sites) == 0);
                lir_code_free(code);
        }
        lir_free(L);
}

static uptr PollPC;
static volatile sig_atomic_t PollInterrupt = 1;

static i32
site_poll(Ty *ty, Value *top, void const *info)
{
        PollPC = site_probe((uptr const **)info);
        return 0;
}

static void
check_poll_site(void)
{
        LirRuntime const *old = lir_runtime();
        LirRuntime runtime = old == NULL ? (LirRuntime) { .current_ty = current_ty } : *old;
        runtime.poll = site_poll;
        runtime.interrupt = &PollInterrupt;
        lir_set_runtime(&runtime);
        LirType type = LIR_TYPE_PTR;
        Lir *L = function(LIR_TYPE_I64, &type, 1);
        CHECK(lir_pc_param(L, 0));
        uptr const *slot = NULL;
        LirLabel end = lir_label(L);
        LirInst poll = {
                .op = LIR_POLL, .dst = LIR_NONE,
                .args = { lir_i((uptr)&EmptyTy), lir_i(0),
                          lir_i((uptr)&slot), lir_l(end) },
                .nargs = 4, .flags = LIR_CALL_SITE, .tag = 43
        };
        CHECK(lir_emit(L, &poll));
        CHECK(lir_bind(L, end));
        ret(L, lir_i(1));
        LirError err;
        LirCode *code = lir_finish(L, false, &err);
        CHECK(code != NULL);
        if (code != NULL) {
                i64 (*body)(uptr const **) = code->body;
                CHECK(body(&slot) == 1);
                CHECK(code->nsites == 1 && code->sites[0].tag == 43);
                CHECK(PollPC - (uptr)code->body == code->sites[0].pc);
                lir_code_free(code);
        }
        lir_free(L);
        lir_set_runtime(old);
}

static u64
random_bits(u64 *seed)
{
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        return *seed;
}

static void
check_fuzz(void)
{
        u64 seed = 0xd7046bfea93c8521;
        char const *env = getenv("TY_LIR_FUZZ");
        u32 count = env == NULL ? 2000 : strtoul(env, NULL, 10);
        LirOp integers[] = {
                LIR_ADD, LIR_SUB, LIR_MUL, LIR_AND, LIR_OR, LIR_XOR,
                LIR_SHL, LIR_SHR, LIR_SAR, LIR_ROTR, LIR_MULHS, LIR_MULHU,
                LIR_SDIV, LIR_UDIV, LIR_SREM, LIR_UREM
        };
        LirOp floats[] = { LIR_FADD, LIR_FSUB, LIR_FMUL, LIR_FDIV, LIR_FMIN, LIR_FMAX };
        for (u32 n = 0; n < count; ++n) {
                bool f = n % 2;
                LirType types[8];
                LirScalar args[8];
                for (u32 i = 0; i < countof(types); ++i) {
                        types[i] = f ? LIR_TYPE_F64 : LIR_TYPE_I64;
                        u64 bits = random_bits(&seed);
                        args[i] = f ? (LirScalar) { .f64 = (i32)(bits % 257) - 128.25 }
                                    : (LirScalar) { .u = bits };
                }
                Lir *L = function(types[0], types, countof(types));
                for (u32 i = 0; i < 24; ++i) {
                        u32 a = random_bits(&seed) % 8;
                        u32 b = random_bits(&seed) % 8;
                        u32 d = random_bits(&seed) % 8;
                        u32 k = random_bits(&seed);
                        LirOp op = f ? floats[k % countof(floats)] : integers[k % countof(integers)];
                        LirOpnd rhs = lir_r(L->params[b]);
                        if ((k & 3) == 0 || op == LIR_FDIV) {
                                rhs = f ? lir_f((k % 16) + 0.25) : lir_i((k % 64) + 1);
                        }
                        emit(L, op, L->params[d], (LirOpnd[]) { lir_r(L->params[a]), rhs }, 2);
                }
                u32 r = random_bits(&seed) % 8;
                ret(L, lir_r(L->params[r]));
                LirError err;
                LirScalar expected = {0};
                CHECK(lir_interpret(NULL, L, args, countof(args), &expected, &err));
                LirScalar actual = execute(NULL, L, args, countof(args));
                bool equal = f ? actual.f64 == expected.f64
                                  || (isnan(actual.f64) && isnan(expected.f64)) : actual.u == expected.u;
                if (!equal) {
                        fprintf(stderr, "fuzz case %u: expected 0x%016" PRIx64 ", got 0x%016" PRIx64 "\n",
                                n, expected.u, actual.u);
                        lir_dump(L, stderr);
                }
                CHECK(equal);
                lir_free(L);
                if (!equal) {
                        break;
                }
        }
}



static i64
weighted12(i64 a, i64 b, i64 c, i64 d, i64 e, i64 f,
           i64 g, i64 h, i64 i, i64 j, i64 k, i64 l)
{
        return a + 3*b + 5*c + 7*d + 11*e + 13*f
             + 17*g + 19*h + 23*i + 29*j + 31*k + 37*l;
}

static void
check_stack_tailcall(void)
{
        LirType types[12];
        LirScalar args[12];
        LirOpnd operands[12];
        for (u32 i = 0; i < countof(types); ++i) {
                types[i] = LIR_TYPE_I64;
                args[i].i = i + 1;
        }
        Lir *L = function(LIR_TYPE_I64, types, countof(types));
        for (u32 i = 0; i < countof(operands); ++i) {
                operands[i] = lir_r(L->params[11 - i]);
        }
        LirInst in = {
                .op = LIR_TAILCALL, .dst = LIR_NONE,
                .args = { lir_i((uptr)weighted12) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_I64, .params = types,
                         .nparams = countof(types), .nfixed = countof(types) },
                .call_args = operands, .ncall_args = countof(operands)
        };
        CHECK(lir_emit(L, &in));
        i64 expected = weighted12(12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1);
        CHECK(execute(NULL, L, args, countof(args)).i == expected);
        lir_free(L);
}


static void
check_cas_parameters(void)
{
        LirType types[] = { LIR_TYPE_I64, LIR_TYPE_PTR, LIR_TYPE_I64 };
        Lir *L = function(LIR_TYPE_I64, types, countof(types));
        LirReg d = lir_reg(L, LIR_I64);
        LirOpnd operands[] = {
                lir_m(L->params[1], LIR_NONE, 1, 0),
                lir_r(L->params[2]), lir_r(L->params[0])
        };
        emit(L, LIR_CAS, d, operands, countof(operands));
        ret(L, lir_r(d));
        i64 value = 7;
        LirScalar args[] = { { .i = 23 }, { .ptr = &value }, { .i = 7 } };
        CHECK(execute(NULL, L, args, countof(args)).i == 7);
        CHECK(value == 23);
        CHECK(execute(NULL, L, args, countof(args)).i == 23);
        CHECK(value == 23);
        lir_free(L);
}

static void
check_raw_native(void)
{
        LirType type = LIR_TYPE_I64;
        LirType types[] = { type, type };
        Lir *L = function(type, types, countof(types));
        LirReg d = lir_reg(L, LIR_I64);
        u32 words[] = { 0x91000400 };
        u8 bytes[] = { 0x48, 0x83, 0xc0, 0x01 };
        LirRawBinding input = { .reg = L->params[0], .phys = 0 };
        LirRawBinding output = { .reg = d, .phys = 0 };
        LirInst in = {
                .op = LIR_RAW, .dst = LIR_NONE,
                .raw = { .arm64 = words, .narm64 = countof(words),
                         .x64 = bytes, .nx64 = countof(bytes),
                         .in = &input, .nin = 1, .out = &output, .nout = 1,
                         .gpr_clobber = 1 }
        };
        CHECK(lir_emit(L, &in));
        emit(L, LIR_ADD, d, (LirOpnd[]) { lir_r(d), lir_r(L->params[0]) }, 2);
        emit(L, LIR_ADD, d, (LirOpnd[]) { lir_r(d), lir_r(L->params[1]) }, 2);
        ret(L, lir_r(d));
        LirScalar args[] = { { .i = 7 }, { .i = 19 } };
        CHECK(execute(NULL, L, args, countof(args)).i == 34);
        lir_free(L);
}

static void
check_division_edges(void)
{
        LirOp ops[] = { LIR_SDIV, LIR_UDIV, LIR_SREM, LIR_UREM };
        for (u32 w = 0; w < 2; ++w) {
                LirClass cls = w ? LIR_I64 : LIR_I32;
                for (u32 i = 0; i < countof(ops); ++i) {
                        bool rem = ops[i] == LIR_SREM || ops[i] == LIR_UREM;
                        LirScalar x = { .u = w ? UINT64_MAX : UINT32_MAX };
                        LirScalar actual = numeric(ops[i], cls, x, (LirScalar) {0}, (LirScalar) {0});
                        CHECK(actual.i == (rem ? -1 : 0));
                }
                LirScalar x = { .i = w ? INT64_MIN : INT32_MIN };
                LirScalar y = { .i = -1 };
                CHECK(numeric(LIR_SDIV, cls, x, y, (LirScalar) {0}).i == x.i);
                CHECK(numeric(LIR_SREM, cls, x, y, (LirScalar) {0}).i == 0);
        }
}

static void
check_distant_targets(void)
{
        LirType type = LIR_TYPE_I64;
        Lir *L = function(LIR_TYPE_F64, &type, 1);
        LirReg value = lir_reg(L, LIR_F64);
        LirLabel near = lir_label(L);
        LirLabel far = lir_label(L);
        emit(L, LIR_FLI, value, (LirOpnd[]) { lir_f(5.5) }, 1);
        LirInst dispatch = {
                .op = LIR_SWITCH, .dst = LIR_NONE,
                .args = { lir_r(L->params[0]), lir_l(far) }, .nargs = 2,
                .targets = &near, .ntargets = 1
        };
        CHECK(lir_emit(L, &dispatch));
        CHECK(lir_bind(L, near));
        emit(L, LIR_BR, LIR_NONE,
             (LirOpnd[]) { lir_cc(LIR_EQ), lir_r(L->params[0]),
                          lir_i(1), lir_l(far) }, 4);
        u32 n = 300000;
        u32 *words = malloc(n * sizeof *words);
        u8 *bytes = malloc(n * 4);
        CHECK(words != NULL && bytes != NULL);
        if (words == NULL || bytes == NULL) {
                free(words);
                free(bytes);
                lir_free(L);
                return;
        }
        for (u32 i = 0; i < n; ++i) {
                words[i] = 0xd503201f;
        }
        memset(bytes, 0x90, n * 4);
        LirInst padding = {
                .op = LIR_RAW, .dst = LIR_NONE,
                .raw = { .arm64 = words, .narm64 = n,
                         .x64 = bytes, .nx64 = n * 4 }
        };
        CHECK(lir_emit(L, &padding));
        free(words);
        free(bytes);
        CHECK(lir_bind(L, far));
        ret(L, lir_r(value));
        LirScalar arg = { .i = 0 };
        CHECK(execute(NULL, L, &arg, 1).f64 == 5.5);
        arg.i = 1;
        CHECK(execute(NULL, L, &arg, 1).f64 == 5.5);
        lir_free(L);
}

int
main(void)
{
        native_scalar_main();
        check_immediates();
        check_native_pressure();
        check_spilled_branches();
        check_native_entry();
        check_sites();
        check_poll_site();
        check_tail_loop();
        check_stack_tailcall();
        check_cas_parameters();
        check_raw_native();
        check_division_edges();
        check_distant_targets();
        check_fuzz();
        printf("LIR native: %u checks, %u failures\n", checks, failures);
        return failures != 0;
}
