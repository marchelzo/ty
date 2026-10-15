#include "scalar.h"

static ffi_type *const FfiTypes[LT_COUNT] = {
        [LT_VOID] = &ffi_type_void,
        [LT_I8]   = &ffi_type_sint8,
        [LT_U8]   = &ffi_type_uint8,
        [LT_I16]  = &ffi_type_sint16,
        [LT_U16]  = &ffi_type_uint16,
        [LT_I32]  = &ffi_type_sint32,
        [LT_U32]  = &ffi_type_uint32,
        [LT_I64]  = &ffi_type_sint64,
        [LT_U64]  = &ffi_type_uint64,
        [LT_F32]  = &ffi_type_float,
        [LT_F64]  = &ffi_type_double,
        [LT_BOOL] = &ffi_type_uint8,
        [LT_PTR]  = &ffi_type_pointer,
        [LT_REF]  = &ffi_type_pointer,
        [LT_VAL]  = &ffi_type_pointer
};

static bool
native(Ty *vm, Lir *L, LirScalar const *args, u32 n, LirScalar *out, LirError *err)
{
        LirCode *code = lir_finish(ty, L, false, err);

        if (code == NULL) {
                return false;
        }

        ffi_type *types[n + 1];
        void     *values[n + 1];
        ffi_cif   cif;

        for (u32 i = 0; i < n; ++i) {
                types[i]  = FfiTypes[L->sig.params[i]];
                values[i] = (void *)&args[i];
        }

        ffi_type *rtype = FfiTypes[L->sig.ret];

        CHECK(ffi_prep_cif(&cif, FFI_DEFAULT_ABI, n, rtype, types) == FFI_OK);
        ffi_call(&cif, FFI_FN(code->body), out, values);

        if (L->sig.ret == LT_I32) {
                out->i = (i32)out->u;
        }

        lir_code_free(code);

        return true;
}

static LirScalar
reference(Lir *L, LirScalar const *args, u32 n)
{
        LirError  err;
        LirScalar want = {0};

        CHECK(lir_interpret(NULL, L, args, n, &want, &err));

        return want;
}

static void
agrees(Lir *L, LirScalar const *args, u32 n)
{
        LirScalar want = reference(L, args, n);
        CHECK(invoke(NULL, L, args, n).u == want.u);
}

static LirCode *
compile(Lir *L)
{
        LirError err;
        LirCode *code = lir_finish(ty, L, false, &err);

        CHECK(code != NULL);

        return code;
}

static void
check_immediates(void)
{
        static i64 const values[] = {
                INT64_MIN, INT64_MAX, -16773120, -4096, -4095, -1,
                0, 1, 4095, 4096, 16773120, 16773121
        };

        for (u32 wide = 0; wide < 2; ++wide) {
                LirType  type = wide ? LT_I64 : LT_I32;
                LirClass cls  = wide ? LIR_I64 : LIR_I32;
                for (LirOp op = LIR_ADD; op <= LIR_SUB; ++op) {
                        for (u32 i = 0; i < countof(values); ++i) {
                                Lir   *L = fn(type, type);
                                LirReg a = L->params[0];

                                if (!wide) {
                                        a = lir_reg(L, LIR_I32);
                                        put(L, LIR_ZEXT32, a, lir_r(L->params[0]));
                                }

                                LirReg d = lir_reg(L, cls);

                                put(L, op, d, lir_r(a), lir_i(values[i]));
                                ret(L, d);

                                LirScalar arg = S(u, wide ? INT64_MAX - 7 : INT32_MAX - 7);
                                agrees(L, &arg, 1);

                                lir_free(L);
                        }
                }
        }
}

static void
check_native_pressure(void)
{
        LirType   types[48];
        LirScalar args[48];

        for (u32 f = 0; f < 2; ++f) {
                for (u32 i = 0; i < countof(types); ++i) {
                        types[i] = f ? LT_F64 : LT_I64;
                        args[i]  = f ? S(f64, i + 0.25) : S(i, i);
                }

                Lir   *L   = fna(types[0], types);
                LirReg acc = lir_reg(L, f ? LIR_F64 : LIR_I64);
                LirOp  add = f ? LIR_FADD : LIR_ADD;

                put(L, f ? LIR_FLI : LIR_LI, acc, f ? lir_f(0.0) : lir_i(0));

                for (u32 i = 0; i < countof(types); ++i) {
                        put(L, add, acc, lir_r(acc), lir_r(L->params[i]));
                }

                ret(L, acc);
                agrees(L, args, countof(args));

                lir_free(L);
        }
}

static void
check_spilled_branches(void)
{
        LirType   types[48];
        LirScalar args[48];

        for (u32 i = 0; i < countof(types); ++i) {
                types[i] = LT_I64;
                args[i]  = S(u, i % 3);
        }

        Lir   *L   = fna(LT_I64, types);
        LirReg acc = lir_reg(L, LIR_I64);

        put(L, LIR_LI, acc, lir_i(0));

        for (u32 i = 0; i < countof(types); ++i) {
                LirOpnd  x    = lir_r(L->params[i]);
                LirLabel next = lir_label(L);

                put(L, LIR_BRZ, LIR_NONE, x, lir_l(next));
                put(L, LIR_ADD, acc, lir_r(acc), lir_i(1));
                here(L, next);

                LirLabel hit  = lir_label(L);
                LirLabel miss = lir_label(L);
                LirLabel end  = lir_label(L);

                push(L, jump_table(x, miss, &hit, 1));
                here(L, hit);
                put(L, LIR_ADD, acc, lir_r(acc), lir_i(3));
                put(L, LIR_JMP, LIR_NONE, lir_l(end));
                here(L, miss);
                put(L, LIR_ADD, acc, lir_r(acc), lir_i(7));
                here(L, end);
        }

        for (u32 i = 0; i < countof(types); ++i) {
                put(L, LIR_ADD, acc, lir_r(acc), lir_r(L->params[i]));
        }

        ret(L, acc);
        agrees(L, args, countof(args));

        lir_free(L);
}

static void
check_native_entry(void)
{
        Lir *L = fn(LT_I64, LT_I64, LT_I64);

        CHECK(lir_pin_param(L, LIR_PIN_0, 0));

        LirLabel entry = lir_label(L);

        put(L, LIR_BRNZ, LIR_NONE, lir_r(L->params[1]), lir_l(entry));
        ret(L, lir_i(7));
        CHECK(lir_entry(L, entry));
        ret(L, lir_pinned(L, LIR_PIN_0));

        CHECK(run(L, S(i, 99), S(i, 0)).i == 7);
        CHECK(run(L, S(i, 99), S(i, 1)).i == 99);

        LirCode *code = compile(L);

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
        Lir     *L   = fn(LT_I64, LT_PTR, LT_I64);
        LirReg   n   = L->params[1];
        LirLabel end = lir_label(L);
        LirOpnd  args[] = { lir_r(L->params[0]), lir_r(n) };

        put(L, LIR_BRZ, LIR_NONE, lir_r(n), lir_l(end));
        put(L, LIR_SUB, n, lir_r(n), lir_i(1));
        push(L, tail(lir_r(L->params[0]), L->sig, args));
        here(L, end);
        ret(L, lir_i(0));

        LirCode *code = compile(L);

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
        Lir *L = fn(LT_U64, LT_PTR);

        CHECK(lir_pc_param(L, 0));

        LirReg  frame = lir_reg(L, LIR_PTR);
        LirReg  d     = lir_reg(L, LIR_I64);
        LirOpnd pc    = lir_r(L->params[0]);
        LirInst in    = call(callee(site_probe), d, sig(LT_U64, T(LT_PTR), 1), &pc);

        in.flags = LIR_CALL_SITE | LIR_RETURNS_TWICE;
        in.tag   = 37;

        put(L, LIR_ALLOCA, frame, lir_i(65536), lir_i(16));
        put(L, LIR_SITE, LIR_NONE, lir_i(13));
        push(L, in);
        ret(L, d);

        LirCode *code = compile(L);

        if (code != NULL) {
                uptr const *slot = NULL;
                u64 (*body)(uptr const **) = code->body;
                u64 address = body(&slot);

                LirImage const *header = (LirImage *)code->body - 1;
                LirSite const  *sites  = (void *)((u8 *)code->body + header->table);

                CHECK(code->nsites == 2);
                CHECK(address - (uptr)code->body == code->sites[1].pc);
                CHECK(code->sites[0].tag == 13 && code->sites[1].tag == 37);
                CHECK(header->size == code->size && header->nsites == code->nsites);
                CHECK(memcmp(sites, code->sites, code->nsites * sizeof *sites) == 0);

                lir_code_free(code);
        }

        lir_free(L);
}

static uptr                  PollPC;
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
        LirRuntime        rt  = { .current_ty = current_ty };

        if (old != NULL) {
                rt = *old;
        }

        rt.poll      = site_poll;
        rt.interrupt = &PollInterrupt;
        lir_set_runtime(&rt);

        Lir *L = fn(LT_I64, LT_PTR);

        CHECK(lir_pc_param(L, 0));

        uptr const *slot = NULL;
        LirLabel    end  = lir_label(L);

        push(L, (LirInst) {
                .op    = LIR_POLL,
                .dst   = LIR_NONE,
                .args  = { callee(&EmptyTy), lir_i(0), callee(&slot), lir_l(end) },
                .nargs = 4,
                .flags = LIR_CALL_SITE,
                .tag   = 43
        });
        here(L, end);
        ret(L, lir_i(1));

        LirCode *code = compile(L);

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

static bool
same(bool f, LirScalar a, LirScalar b)
{
        if (!f) {
                return a.u == b.u;
        }

        return (a.f64 == b.f64) || (isnan(a.f64) && isnan(b.f64));
}

static void
check_fuzz(void)
{
        static LirOp const ints[] = {
                LIR_ADD,   LIR_SUB,   LIR_MUL,  LIR_AND,  LIR_OR,    LIR_XOR,
                LIR_SHL,   LIR_SHR,   LIR_SAR,  LIR_ROTR, LIR_MULHS, LIR_MULHU,
                LIR_SDIV,  LIR_UDIV,  LIR_SREM, LIR_UREM
        };
        static LirOp const floats[] = {
                LIR_FADD, LIR_FSUB, LIR_FMUL, LIR_FDIV, LIR_FMIN, LIR_FMAX
        };

        u64         seed  = 0xd7046bfea93c8521;
        char const *env   = getenv("TY_LIR_FUZZ");
        u32         count = (env == NULL) ? 2000 : strtoul(env, NULL, 10);

        for (u32 n = 0; n < count; ++n) {
                bool         f    = n % 2;
                LirOp const *ops  = f ? floats : ints;
                u32          nops = f ? countof(floats) : countof(ints);
                LirType      types[8];
                LirScalar    args[8];

                for (u32 i = 0; i < countof(types); ++i) {
                        u64 bits = xorshift(&seed);
                        types[i] = f ? LT_F64 : LT_I64;
                        args[i]  = f ? S(f64, (i32)(bits % 257) - 128.25) : S(u, bits);
                }

                Lir *L = fna(types[0], types);

                for (u32 i = 0; i < 24; ++i) {
                        u32     a   = xorshift(&seed) % 8;
                        u32     b   = xorshift(&seed) % 8;
                        u32     d   = xorshift(&seed) % 8;
                        u32     k   = xorshift(&seed);
                        LirOp   op  = ops[k % nops];
                        LirOpnd rhs = lir_r(L->params[b]);

                        if ((k & 3) == 0 || op == LIR_FDIV) {
                                rhs = f ? lir_f((k % 16) + 0.25) : lir_i((k % 64) + 1);
                        }

                        put(L, op, L->params[d], lir_r(L->params[a]), rhs);
                }

                ret(L, L->params[xorshift(&seed) % 8]);

                LirScalar want = reference(L, args, countof(args));
                LirScalar got  = invoke(NULL, L, args, countof(args));
                bool      ok   = same(f, got, want);

                if (!ok) {
                        fprintf(
                                stderr,
                                "fuzz case %u: expected 0x%016" PRIx64
                                ", got 0x%016" PRIx64 "\n",
                                n,
                                want.u,
                                got.u
                        );
                        lir_dump(L, stderr);
                }

                CHECK(ok);
                lir_free(L);

                if (!ok) {
                        break;
                }
        }
}

static i64
weighted12(
        i64 a, i64 b, i64 c, i64 d, i64 e, i64 f,
        i64 g, i64 h, i64 i, i64 j, i64 k, i64 l
)
{
        return a + 3*b + 5*c + 7*d + 11*e + 13*f
             + 17*g + 19*h + 23*i + 29*j + 31*k + 37*l;
}

static void
check_stack_tailcall(void)
{
        LirType   types[12];
        LirScalar args[12];
        LirOpnd   reversed[12];

        for (u32 i = 0; i < countof(types); ++i) {
                types[i] = LT_I64;
                args[i]  = S(i, i + 1);
        }

        Lir *L = fna(LT_I64, types);

        for (u32 i = 0; i < countof(reversed); ++i) {
                reversed[i] = lir_r(L->params[11 - i]);
        }

        push(L, tail(callee(weighted12), sig(LT_I64, types, countof(types)), reversed));

        i64 want = weighted12(12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1);
        CHECK(invoke(NULL, L, args, countof(args)).i == want);

        lir_free(L);
}

static void
check_cas_parameters(void)
{
        Lir    *L   = fn(LT_I64, LT_I64, LT_PTR, LT_I64);
        LirReg  d   = lir_reg(L, LIR_I64);
        LirOpnd mem = deref(L->params[1], 0);

        put(L, LIR_CAS, d, mem, lir_r(L->params[2]), lir_r(L->params[0]));
        ret(L, d);

        i64 value = 7;

        CHECK(run(L, S(i, 23), S(ptr, &value), S(i, 7)).i == 7);
        CHECK(value == 23);
        CHECK(run(L, S(i, 23), S(ptr, &value), S(i, 7)).i == 23);
        CHECK(value == 23);

        lir_free(L);
}

static void
check_raw_native(void)
{
        Lir          *L    = fn(LT_I64, LT_I64, LT_I64);
        LirReg        d    = lir_reg(L, LIR_I64);
        u32           a64[] = { 0x91000400 };
        u8            x64[] = { 0x48, 0x83, 0xc0, 0x01 };
        LirRawBinding in   = { .reg = L->params[0], .phys = 0 };
        LirRawBinding out  = { .reg = d, .phys = 0 };

        push(L, (LirInst) {
                .op  = LIR_RAW,
                .dst = LIR_NONE,
                .raw = {
                        .arm64       = a64,
                        .narm64      = countof(a64),
                        .x64         = x64,
                        .nx64        = countof(x64),
                        .in          = &in,
                        .nin         = 1,
                        .out         = &out,
                        .nout        = 1,
                        .gpr_clobber = 1
                }
        });
        put(L, LIR_ADD, d, lir_r(d), lir_r(L->params[0]));
        put(L, LIR_ADD, d, lir_r(d), lir_r(L->params[1]));
        ret(L, d);

        CHECK(run(L, S(i, 7), S(i, 19)).i == 34);

        lir_free(L);
}

static void
check_division_edges(void)
{
        static LirOp const ops[] = { LIR_SDIV, LIR_UDIV, LIR_SREM, LIR_UREM };

        for (u32 wide = 0; wide < 2; ++wide) {
                LirClass cls = wide ? LIR_I64 : LIR_I32;

                for (u32 i = 0; i < countof(ops); ++i) {
                        bool      rem = (ops[i] == LIR_SREM) || (ops[i] == LIR_UREM);
                        LirScalar x   = S(u, wide ? UINT64_MAX : UINT32_MAX);
                        CHECK(numeric(ops[i], cls, x, S0, S0).i == (rem ? -1 : 0));
                }

                LirScalar min = S(i, wide ? INT64_MIN : INT32_MIN);
                CHECK(numeric(LIR_SDIV, cls, min, S(i, -1), S0).i == min.i);
                CHECK(numeric(LIR_SREM, cls, min, S(i, -1), S0).i == 0);
        }
}

static void
check_constant_division(void)
{
        static LirOp const ops[] = { LIR_SDIV, LIR_UDIV, LIR_SREM, LIR_UREM };
        u64 divisors[384] = { 0, 1, 2, 3, 5, 7, 10, 60, 255, 1000, 1280, 86400 };
        u32 count = 12;
        u64 seed = 0xb71e820c59a463fd;

        for (u32 bit = 1; bit < 64; ++bit) {
                u64 d = (u64)1 << bit;
                divisors[count++] = d - 1;
                divisors[count++] = d;
                divisors[count++] = d + 1;
                divisors[count++] = 0 - d - 1;
                divisors[count++] = 0 - d + 1;
        }

        while (count < countof(divisors)) {
                divisors[count++] = xorshift(&seed);
        }

        for (u32 wide = 0; wide < 2; ++wide) {
                LirType type = wide ? LT_I64 : LT_I32;
                LirClass cls = wide ? LIR_I64 : LIR_I32;
                u64 high = wide ? (u64)1 << 63 : (u64)1 << 31;

                for (u32 op = 0; op < countof(ops); ++op) {
                        for (u32 i = 0; i < count; ++i) {
                                Lir *L = fn(type, type);
                                LirReg dst = lir_reg(L, cls);
                                LirReg x = L->params[0];
                                LirOpnd rhs = lir_i(divisors[i]);

                                if (!wide) {
                                        x = lir_reg(L, cls);
                                        put(L, LIR_ZEXT32, x, lir_r(L->params[0]));
                                }

                                if ((i & 1) != 0) {
                                        LirReg a = lir_reg(L, cls);
                                        LirReg b = lir_reg(L, cls);
                                        put(L, LIR_LI, a, rhs);
                                        put(L, LIR_MOV, b, lir_r(a));
                                        rhs = lir_r(b);
                                }

                                put(L, ops[op], dst, lir_r(x), rhs);
                                ret(L, dst);

                                LirCode *code = compile(L);
                                u64 edges[] = {
                                        0, 1, UINT64_MAX, high, high - 1, high + 1,
                                        divisors[i] - 1, divisors[i], divisors[i] + 1,
                                        0 - divisors[i], 2 * divisors[i] - 1,
                                        2 * divisors[i], 2 * divisors[i] + 1
                                };

                                for (u32 j = 0; j < countof(edges) + 64; ++j) {
                                        u64 bits = (j < countof(edges)) ? edges[j] : xorshift(&seed);
                                        LirScalar arg = S(u, bits);
                                        LirScalar want = reference(L, &arg, 1);
                                        i64 got;

                                        if (wide) {
                                                got = ((i64 (*)(i64))code->body)(bits);
                                        } else {
                                                got = ((i32 (*)(i32))code->body)(bits);
                                        }

                                        if ((u64)got != want.u) {
                                                fprintf(stderr, "%s i%u x=%" PRIx64 " d=%" PRIx64 "\n",
                                                        LirOps[ops[op]].name, wide ? 64 : 32, bits, divisors[i]);
                                        }
                                        CHECK((u64)got == want.u);
                                }

                                lir_code_free(code);
                                lir_free(L);
                        }
                }
        }
}

static void
check_mutable_divisor(void)
{
        Lir *L = fn(LT_I64, LT_I64);
        LirReg d = lir_reg(L, LIR_I64);
        LirReg q = lir_reg(L, LIR_I64);
        LirReg sum = lir_reg(L, LIR_I64);
        LirLabel loop = lir_label(L);

        put(L, LIR_LI, d, lir_i(1));
        put(L, LIR_LI, sum, lir_i(0));
        here(L, loop);
        put(L, LIR_SDIV, q, lir_r(L->params[0]), lir_r(d));
        put(L, LIR_ADD, sum, lir_r(sum), lir_r(q));
        put(L, LIR_ADD, d, lir_r(d), lir_i(1));
        put(L, LIR_BR, LIR_NONE, lir_cc(LIR_LT), lir_r(d), lir_i(25), lir_l(loop));
        ret(L, sum);

        LirScalar arg = S(i, 12345);

        agrees(L, &arg, 1);
        lir_free(L);
}

static void
check_distant_targets(void)
{
        enum { PAD = 300000 };

        Lir     *L     = fn(LT_F64, LT_I64);
        LirReg   value = lir_reg(L, LIR_F64);
        LirLabel near  = lir_label(L);
        LirLabel far   = lir_label(L);

        put(L, LIR_FLI, value, lir_f(5.5));
        push(L, jump_table(lir_r(L->params[0]), far, &near, 1));
        here(L, near);
        put(L, LIR_BR, LIR_NONE, lir_cc(LIR_EQ), lir_r(L->params[0]), lir_i(1), lir_l(far));

        u32 *nops = xtA(u32, PAD);
        u8  *x64  = xmA(PAD * 4);

        for (u32 i = 0; i < PAD; ++i) {
                nops[i] = 0xd503201f;
        }

        memset(x64, 0x90, PAD * 4);

        push(L, (LirInst) {
                .op  = LIR_RAW,
                .dst = LIR_NONE,
                .raw = { .arm64 = nops, .narm64 = PAD, .x64 = x64, .nx64 = PAD * 4 }
        });

        xmF(nops);
        xmF(x64);

        here(L, far);
        ret(L, value);

        CHECK(run(L, S(i, 0)).f64 == 5.5);
        CHECK(run(L, S(i, 1)).f64 == 5.5);

        lir_free(L);
}

int
main(void)
{
        scalar_suite(native, true);
        report("LIR native scalars");

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
        check_constant_division();
        check_mutable_divisor();
        check_distant_targets();
        check_fuzz();

        return report("LIR native");
}
