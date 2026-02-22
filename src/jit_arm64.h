/*
** This file has been pre-processed with DynASM.
** https://luajit.org/dynasm.html
** DynASM version 1.5.0, DynASM arm version 1.5.0
** DO NOT EDIT! The original file is in "src/jit_arm64.dasc".
*/

#line 1 "src/jit_arm64.dasc"
// jit_arm64.dasc - DynASM ARM64 code generation templates for ty JIT
//
// Processed by: luajit LuaJIT/dynasm/dynasm.lua -o src/jit_arm64.h src/jit_arm64.dasc
//
// The generated jit_arm64.h is included by src/jit.c
//

//|.arch arm64
#if DASM_VERSION != 10500
#error "Version mismatch between DynASM and included encoding engine"
#endif
#line 9 "src/jit_arm64.dasc"
//|.actionlist jit_actions
static const unsigned int jit_actions[269] = {
0x8b000000,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0xcb000000,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0x9b007c00,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0x9ac00c00,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0x9ac00c10,
0x00110005,
0x00110010,
0x9b008200,
0x00110000,
0x00110010,
0x0011000a,
0x00000000,
0xcb0003e0,
0x00110000,
0x00110010,
0x00000000,
0x8a000000,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0xaa000000,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0xca000000,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0x9ac02000,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0x9ac02800,
0x00110000,
0x00110005,
0x00110010,
0x00000000,
0xd2800000,
0x00110000,
0x000a0205,
0x00000000,
0x92800000,
0x00110000,
0x000a0205,
0x00000000,
0xd2800000,
0x00110000,
0x000a0205,
0x00000000,
0xf2a00000,
0x00110000,
0x000a0205,
0x00000000,
0xf2c00000,
0x00110000,
0x000a0205,
0x00000000,
0xf2e00000,
0x00110000,
0x000a0205,
0x00000000,
0xaa0003e0,
0x00110000,
0x00110010,
0x00000000,
0xeb00001f,
0x00110005,
0x00110010,
0x9a9f17e0,
0x00110000,
0x00000000,
0xeb00001f,
0x00110005,
0x00110010,
0x9a9f07e0,
0x00110000,
0x00000000,
0xeb00001f,
0x00110005,
0x00110010,
0x9a9fa7e0,
0x00110000,
0x00000000,
0xeb00001f,
0x00110005,
0x00110010,
0x9a9fc7e0,
0x00110000,
0x00000000,
0xeb00001f,
0x00110005,
0x00110010,
0x9a9fd7e0,
0x00110000,
0x00000000,
0xeb00001f,
0x00110005,
0x00110010,
0x9a9fb7e0,
0x00110000,
0x00000000,
0xb4000000,
0x00110000,
0x00070800,
0x00000000,
0xb5000000,
0x00110000,
0x00070800,
0x00000000,
0x14000000,
0x00070000,
0x00000000,
0x00080000,
0x00000000,
0x00060014,
0xa9bf7bfd,
0x910003fd,
0xa9bf53f3,
0xa9bf5bf5,
0xa9bf63f7,
0x00000000,
0xaa0003f3,
0xaa0103f4,
0xaa0203f5,
0xaa0303f6,
0x00000000,
0xf8400269,
0x000f0003,
0xcb0902b8,
0x00000000,
0x910002b7,
0x000c0000,
0x00000000,
0xaa1503f7,
0x00000000,
0xa8c163f7,
0xa8c15bf5,
0xa8c153f3,
0xa8c17bfd,
0xd65f03c0,
0x00000000,
0xf8400269,
0x000f0003,
0x8b180135,
0x00000000,
0x910002b7,
0x000c0000,
0x00000000,
0xaa1503f7,
0x00000000,
0xd345ff10,
0x00000000,
0x91000210,
0x000c0000,
0x00000000,
0xf8000270,
0x000f0003,
0x00000000,
0xf8400000,
0x00110000,
0x00110005,
0x000f0003,
0x00000000,
0xf8000000,
0x00110000,
0x00110005,
0x000f0003,
0x00000000,
0x38400000,
0x00110000,
0x00110005,
0x000f0000,
0x00000000,
0x38000000,
0x00110000,
0x00110005,
0x000f0000,
0x00000000,
0x78000000,
0x00110000,
0x00110005,
0x000f0001,
0x00000000,
0xb8000000,
0x00110000,
0x00110005,
0x000f0002,
0x00000000,
0xa9400000,
0x00110000,
0x0011000a,
0x00110005,
0x000a8cef,
0x00000000,
0xa9000000,
0x00110000,
0x0011000a,
0x00110005,
0x000a8cef,
0x00000000,
0xaa0003e0,
0x00110000,
0x00110010,
0x00000000,
0x91000000,
0x00110000,
0x00110005,
0x000c0000,
0x00000000,
0xd63f0000,
0x00110005,
0x00000000,
0xf100001f,
0x00110005,
0x000c0000,
0x00000000,
0x7100001f,
0x00110005,
0x000c0000,
0x00000000,
0x9a9f17f0,
0xb5000010,
0x00070800,
0x00000000,
0x9a9f07f0,
0xb5000010,
0x00070800,
0x00000000,
0x9a9fa7f0,
0xb5000010,
0x00070800,
0x00000000,
0x9a9fd7f0,
0xb5000010,
0x00070800,
0x00000000,
0x9a9fc7f0,
0xb5000010,
0x00070800,
0x00000000,
0x9a9fb7f0,
0xb5000010,
0x00070800,
0x00000000,
0xb8400000,
0x00110000,
0x00110005,
0x000f0002,
0x00000000
};

#line 10 "src/jit_arm64.dasc"
//|.section code
#define DASM_SECTION_CODE	0
#define DASM_MAXSECTION		1
#line 11 "src/jit_arm64.dasc"
//|.globals JIT_GLOB_
enum {
  JIT_GLOB_entry,
  JIT_GLOB__MAX
};
#line 12 "src/jit_arm64.dasc"

// --- Integer arithmetic ---

static void jit_emit_add(dasm_State **Dst, int dst, int left, int right) {
        //|  add Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 0, (dst), (left), (right));
#line 17 "src/jit_arm64.dasc"
}

static void jit_emit_sub(dasm_State **Dst, int dst, int left, int right) {
        //|  sub Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 5, (dst), (left), (right));
#line 21 "src/jit_arm64.dasc"
}

static void jit_emit_mul(dasm_State **Dst, int dst, int left, int right) {
        //|  mul Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 10, (dst), (left), (right));
#line 25 "src/jit_arm64.dasc"
}

static void jit_emit_sdiv(dasm_State **Dst, int dst, int left, int right) {
        //|  sdiv Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 15, (dst), (left), (right));
#line 29 "src/jit_arm64.dasc"
}

static void jit_emit_mod(dasm_State **Dst, int dst, int left, int right) {
        //|  sdiv x16, Rx(left), Rx(right)
        //|  msub Rx(dst), x16, Rx(right), Rx(left)
        dasm_put(Dst, 20, (left), (right), (dst), (right), (left));
#line 34 "src/jit_arm64.dasc"
}

static void jit_emit_neg(dasm_State **Dst, int dst, int src) {
        //|  neg Rx(dst), Rx(src)
        dasm_put(Dst, 28, (dst), (src));
#line 38 "src/jit_arm64.dasc"
}

// --- Bitwise ops ---

static void jit_emit_and(dasm_State **Dst, int dst, int left, int right) {
        //|  and Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 32, (dst), (left), (right));
#line 44 "src/jit_arm64.dasc"
}

static void jit_emit_or(dasm_State **Dst, int dst, int left, int right) {
        //|  orr Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 37, (dst), (left), (right));
#line 48 "src/jit_arm64.dasc"
}

static void jit_emit_xor(dasm_State **Dst, int dst, int left, int right) {
        //|  eor Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 42, (dst), (left), (right));
#line 52 "src/jit_arm64.dasc"
}

static void jit_emit_shl(dasm_State **Dst, int dst, int left, int right) {
        //|  lsl Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 47, (dst), (left), (right));
#line 56 "src/jit_arm64.dasc"
}

static void jit_emit_shr(dasm_State **Dst, int dst, int left, int right) {
        //|  asr Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 52, (dst), (left), (right));
#line 60 "src/jit_arm64.dasc"
}

// --- Load immediate ---

static void jit_emit_load_imm(dasm_State **Dst, int dst, int64_t imm) {
        if (imm >= 0 && imm < 65536) {
                //|  movz Rx(dst), #imm
                dasm_put(Dst, 57, (dst), imm);
#line 67 "src/jit_arm64.dasc"
        } else if (imm >= -65536 && imm < 0) {
                //|  movn Rx(dst), #(~imm)
                dasm_put(Dst, 61, (dst), (~imm));
#line 69 "src/jit_arm64.dasc"
        } else {
                uint64_t u = (uint64_t)imm;
                //|  movz Rx(dst), #(u & 0xFFFF)
                dasm_put(Dst, 65, (dst), (u & 0xFFFF));
#line 72 "src/jit_arm64.dasc"
                if ((u >> 16) & 0xFFFF) {
                        //|  movk Rx(dst), #((u >> 16) & 0xFFFF), lsl #16
                        dasm_put(Dst, 69, (dst), ((u >> 16) & 0xFFFF));
#line 74 "src/jit_arm64.dasc"
                }
                if ((u >> 32) & 0xFFFF) {
                        //|  movk Rx(dst), #((u >> 32) & 0xFFFF), lsl #32
                        dasm_put(Dst, 73, (dst), ((u >> 32) & 0xFFFF));
#line 77 "src/jit_arm64.dasc"
                }
                if ((u >> 48) & 0xFFFF) {
                        //|  movk Rx(dst), #((u >> 48) & 0xFFFF), lsl #48
                        dasm_put(Dst, 77, (dst), ((u >> 48) & 0xFFFF));
#line 80 "src/jit_arm64.dasc"
                }
        }
}

// --- Move between registers ---

static void jit_emit_mov(dasm_State **Dst, int dst, int src) {
        if (dst != src) {
                //|  mov Rx(dst), Rx(src)
                dasm_put(Dst, 81, (dst), (src));
#line 89 "src/jit_arm64.dasc"
        }
}

// --- Comparisons (result is 0 or 1 in dst) ---

static void jit_emit_cmp_eq(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), eq
        dasm_put(Dst, 85, (left), (right), (dst));
#line 97 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_ne(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), ne
        dasm_put(Dst, 91, (left), (right), (dst));
#line 102 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_lt(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), lt
        dasm_put(Dst, 97, (left), (right), (dst));
#line 107 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_le(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), le
        dasm_put(Dst, 103, (left), (right), (dst));
#line 112 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_gt(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), gt
        dasm_put(Dst, 109, (left), (right), (dst));
#line 117 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_ge(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), ge
        dasm_put(Dst, 115, (left), (right), (dst));
#line 122 "src/jit_arm64.dasc"
}

// --- Conditional branches ---

static void jit_emit_cbz(dasm_State **Dst, int reg, int label) {
        //|  cbz Rx(reg), =>label
        dasm_put(Dst, 121, (reg), label);
#line 128 "src/jit_arm64.dasc"
}

static void jit_emit_cbnz(dasm_State **Dst, int reg, int label) {
        //|  cbnz Rx(reg), =>label
        dasm_put(Dst, 125, (reg), label);
#line 132 "src/jit_arm64.dasc"
}

static void jit_emit_jump(dasm_State **Dst, int label) {
        //|  b =>label
        dasm_put(Dst, 129, label);
#line 136 "src/jit_arm64.dasc"
}

static void jit_emit_label(dasm_State **Dst, int label) {
        //|=>label:
        dasm_put(Dst, 132, label);
#line 140 "src/jit_arm64.dasc"
}

// ============================================================================
// GENERIC MODE: Value-typed functions with C helper calls
//
// Calling convention:
//   void fn(Ty *ty, Value *result, Value *args, Value *env)
//   x0=ty, x1=result, x2=args, x3=env
//
// Callee-saved register assignments:
//   x19 = Ty *ty
//   x20 = Value *result
//   x21 = Value *args (== &stack.items[fp])
//   x22 = Value *env
//   x23 = operand base pointer (== &stack.items[fp + bound])
//   x24 = fp byte offset into stack (stable across reallocs)
//
// Value slots live in the interpreter's stack at [x23 + i*32].
// ============================================================================
static void jit_emit_gen_prologue(dasm_State **Dst, int bound) {
        //|->entry:
        //|  stp x29, x30, [sp, #-16]!
        //|  mov x29, sp
        //|  stp x19, x20, [sp, #-16]!
        //|  stp x21, x22, [sp, #-16]!
        //|  stp x23, x24, [sp, #-16]!
        dasm_put(Dst, 134);
#line 166 "src/jit_arm64.dasc"
        // Stash incoming args into callee-saved registers
        //|  mov x19, x0
        //|  mov x20, x1
        //|  mov x21, x2
        //|  mov x22, x3
        dasm_put(Dst, 141);
#line 171 "src/jit_arm64.dasc"
        // x24 = byte offset of fp into stack.items (survives realloc)
        // x24 = args - stack.items
        //|  ldr x9, [x19, #OFF_TY_STACK + OFF_VEC_DATA]
        //|  sub x24, x21, x9
        dasm_put(Dst, 146, OFF_TY_STACK + OFF_VEC_DATA);
#line 175 "src/jit_arm64.dasc"
        // x23 = args + bound * VALUE_SIZE = &stack.items[fp + bound]
        int ops_off = bound * VALUE_SIZE;
        if (ops_off > 0) {
                //|  add x23, x21, #ops_off
                dasm_put(Dst, 150, ops_off);
#line 179 "src/jit_arm64.dasc"
        } else {
                //|  mov x23, x21
                dasm_put(Dst, 153);
#line 181 "src/jit_arm64.dasc"
        }
}

static void jit_emit_gen_epilogue(dasm_State **Dst) {
        //|  ldp x23, x24, [sp], #16
        //|  ldp x21, x22, [sp], #16
        //|  ldp x19, x20, [sp], #16
        //|  ldp x29, x30, [sp], #16
        //|  ret
        dasm_put(Dst, 155);
#line 190 "src/jit_arm64.dasc"
}

// --- Reload x21/x23 after calls that may realloc the stack ---
// x24 holds the stable fp byte offset; bound is known at compile time.
static void jit_emit_reload_stack(dasm_State **Dst, int bound) {
        //|  ldr x9, [x19, #OFF_TY_STACK + OFF_VEC_DATA]
        //|  add x21, x9, x24
        dasm_put(Dst, 161, OFF_TY_STACK + OFF_VEC_DATA);
#line 197 "src/jit_arm64.dasc"
        int ops_off = bound * VALUE_SIZE;
        if (ops_off > 0) {
                //|  add x23, x21, #ops_off
                dasm_put(Dst, 165, ops_off);
#line 200 "src/jit_arm64.dasc"
        } else {
                //|  mov x23, x21
                dasm_put(Dst, 168);
#line 202 "src/jit_arm64.dasc"
        }
}

// Sync interpreter stack count to JIT's current sp.
// Sets ty->stack.count = (fp + bound + sp)
// x24 holds fp * VALUE_SIZE, so fp = x24 / VALUE_SIZE
// But simpler: x23 points to &stack.items[fp + bound],
// and sp slots past that is where we are.
static void jit_emit_sync_stack_count(dasm_State **Dst, int bound, int sp) {
        // stack.count = fp + bound + sp
        // fp * VALUE_SIZE is in x24
        // We need the integer index, not byte offset.
        // fp = x24 / VALUE_SIZE = x24 >> 5  (assuming VALUE_SIZE == 32)
        //|  lsr x16, x24, #5
        dasm_put(Dst, 170);
#line 216 "src/jit_arm64.dasc"
        int total = bound + sp;
        if (total > 0) {
                //|  add x16, x16, #total
                dasm_put(Dst, 172, total);
#line 219 "src/jit_arm64.dasc"
        }
        //|  str x16, [x19, #OFF_TY_STACK + OFF_VEC_LEN]
        dasm_put(Dst, 175, OFF_TY_STACK + OFF_VEC_LEN);
#line 221 "src/jit_arm64.dasc"
}

// --- Memory operations ---

// Load 64-bit from [base + offset]
static void jit_emit_ldr64(dasm_State **Dst, int dst, int base, int offset) {
        //|  ldr Rx(dst), [Rx(base), #offset]
        dasm_put(Dst, 178, (dst), (base), offset);
#line 228 "src/jit_arm64.dasc"
}

// Store 64-bit to [base + offset]
static void jit_emit_str64(dasm_State **Dst, int src, int base, int offset) {
        //|  str Rx(src), [Rx(base), #offset]
        dasm_put(Dst, 183, (src), (base), offset);
#line 233 "src/jit_arm64.dasc"
}

// Load byte from [base + offset]
static void jit_emit_ldrb(dasm_State **Dst, int dst, int base, int offset) {
        //|  ldrb Rw(dst), [Rx(base), #offset]
        dasm_put(Dst, 188, (dst), (base), offset);
#line 238 "src/jit_arm64.dasc"
}

// Store byte to [base + offset]
static void jit_emit_strb(dasm_State **Dst, int src, int base, int offset) {
        //|  strb Rw(src), [Rx(base), #offset]
        dasm_put(Dst, 193, (src), (base), offset);
#line 243 "src/jit_arm64.dasc"
}

// Store halfword (16-bit) to [base + offset]
static void jit_emit_strh(dasm_State **Dst, int src, int base, int offset) {
        //|  strh Rw(src), [Rx(base), #offset]
        dasm_put(Dst, 198, (src), (base), offset);
#line 248 "src/jit_arm64.dasc"
}

// Store 32-bit word to [base + offset]
static void jit_emit_str32(dasm_State **Dst, int src, int base, int offset) {
        //|  str Rw(src), [Rx(base), #offset]
        dasm_put(Dst, 203, (src), (base), offset);
#line 253 "src/jit_arm64.dasc"
}

// Load pair of 64-bit values from [base + offset]
static void jit_emit_ldp64(dasm_State **Dst, int r1, int r2, int base, int offset) {
        //|  ldp Rx(r1), Rx(r2), [Rx(base), #offset]
        dasm_put(Dst, 208, (r1), (r2), (base), offset);
#line 258 "src/jit_arm64.dasc"
}

// Store pair of 64-bit values to [base + offset]
static void jit_emit_stp64(dasm_State **Dst, int r1, int r2, int base, int offset) {
        //|  stp Rx(r1), Rx(r2), [Rx(base), #offset]
        dasm_put(Dst, 214, (r1), (r2), (base), offset);
#line 263 "src/jit_arm64.dasc"
}

// --- Add immediate ---
static void jit_emit_add_imm(dasm_State **Dst, int dst, int src, int imm) {
        if (imm == 0) {
                if (dst != src) {
                        //|  mov Rx(dst), Rx(src)
                        dasm_put(Dst, 220, (dst), (src));
#line 270 "src/jit_arm64.dasc"
                }
        } else {
                //|  add Rx(dst), Rx(src), #imm
                dasm_put(Dst, 224, (dst), (src), imm);
#line 273 "src/jit_arm64.dasc"
        }
}

// --- Indirect call ---
static void jit_emit_call_reg(dasm_State **Dst, int reg) {
        //|  blr Rx(reg)
        dasm_put(Dst, 229, (reg));
#line 279 "src/jit_arm64.dasc"
}

// --- Compare register with immediate ---
static void jit_emit_cmp_ri(dasm_State **Dst, int reg, int imm) {
        //|  cmp Rx(reg), #imm
        dasm_put(Dst, 232, (reg), imm);
#line 284 "src/jit_arm64.dasc"
}

// Compare 32-bit register with immediate (for int return values)
static void jit_emit_cmp_ri32(dasm_State **Dst, int reg, int imm) {
        //|  cmp Rw(reg), #imm
        dasm_put(Dst, 236, (reg), imm);
#line 289 "src/jit_arm64.dasc"
}

// --- Conditional branches (use after cmp_ri) ---

static void jit_emit_branch_eq(dasm_State **Dst, int label) {
        //|  cset x16, eq
        //|  cbnz x16, =>label
        dasm_put(Dst, 240, label);
#line 296 "src/jit_arm64.dasc"
}

static void jit_emit_branch_ne(dasm_State **Dst, int label) {
        //|  cset x16, ne
        //|  cbnz x16, =>label
        dasm_put(Dst, 244, label);
#line 301 "src/jit_arm64.dasc"
}

static void jit_emit_branch_lt(dasm_State **Dst, int label) {
        //|  cset x16, lt
        //|  cbnz x16, =>label
        dasm_put(Dst, 248, label);
#line 306 "src/jit_arm64.dasc"
}

static void jit_emit_branch_gt(dasm_State **Dst, int label) {
        //|  cset x16, gt
        //|  cbnz x16, =>label
        dasm_put(Dst, 252, label);
#line 311 "src/jit_arm64.dasc"
}

static void jit_emit_branch_le(dasm_State **Dst, int label) {
        //|  cset x16, le
        //|  cbnz x16, =>label
        dasm_put(Dst, 256, label);
#line 316 "src/jit_arm64.dasc"
}

static void jit_emit_branch_ge(dasm_State **Dst, int label) {
        //|  cset x16, ge
        //|  cbnz x16, =>label
        dasm_put(Dst, 260, label);
#line 321 "src/jit_arm64.dasc"
}

// Load 32-bit word from [base + offset]
static void jit_emit_ldr32(dasm_State **Dst, int dst, int base, int offset) {
        //|  ldr Rw(dst), [Rx(base), #offset]
        dasm_put(Dst, 264, (dst), (base), offset);
#line 326 "src/jit_arm64.dasc"
}
