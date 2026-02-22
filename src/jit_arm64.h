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
static const unsigned int jit_actions[255] = {
0x00060014,
0x00000000,
0xd65f03c0,
0x00000000,
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
0xd10003ff,
0x000c0000,
0x00000000,
0x910003f7,
0x00000000,
0x910003ff,
0x000c0000,
0x00000000,
0xa8c163f7,
0xa8c15bf5,
0xa8c153f3,
0xa8c17bfd,
0xd65f03c0,
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

// ============================================================================
// INT MODE: Pure integer functions
//
// Calling convention:
//   intmax_t fn(intmax_t a0, intmax_t a1, intmax_t a2, intmax_t a3)
//   Arguments: x0-x3, Return: x0, Scratch: x8-x15
// ============================================================================

//|.define ARG0, x0
//|.define ARG1, x1
//|.define ARG2, x2
//|.define ARG3, x3
//|.define RET,  x0

// Scratch registers for intermediate values (int mode)
//|.define TMP0, x8
//|.define TMP1, x9
//|.define TMP2, x10
//|.define TMP3, x11
//|.define TMP4, x12
//|.define TMP5, x13
//|.define TMP6, x14
//|.define TMP7, x15

static void jit_emit_prologue(dasm_State **Dst) {
        //|->entry:
        dasm_put(Dst, 0);
#line 39 "src/jit_arm64.dasc"
}

static void jit_emit_epilogue(dasm_State **Dst) {
        //|  ret
        dasm_put(Dst, 2);
#line 43 "src/jit_arm64.dasc"
}

// --- Integer arithmetic ---

static void jit_emit_add(dasm_State **Dst, int dst, int left, int right) {
        //|  add Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 4, (dst), (left), (right));
#line 49 "src/jit_arm64.dasc"
}

static void jit_emit_sub(dasm_State **Dst, int dst, int left, int right) {
        //|  sub Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 9, (dst), (left), (right));
#line 53 "src/jit_arm64.dasc"
}

static void jit_emit_mul(dasm_State **Dst, int dst, int left, int right) {
        //|  mul Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 14, (dst), (left), (right));
#line 57 "src/jit_arm64.dasc"
}

static void jit_emit_sdiv(dasm_State **Dst, int dst, int left, int right) {
        //|  sdiv Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 19, (dst), (left), (right));
#line 61 "src/jit_arm64.dasc"
}

static void jit_emit_mod(dasm_State **Dst, int dst, int left, int right) {
        //|  sdiv x16, Rx(left), Rx(right)
        //|  msub Rx(dst), x16, Rx(right), Rx(left)
        dasm_put(Dst, 24, (left), (right), (dst), (right), (left));
#line 66 "src/jit_arm64.dasc"
}

static void jit_emit_neg(dasm_State **Dst, int dst, int src) {
        //|  neg Rx(dst), Rx(src)
        dasm_put(Dst, 32, (dst), (src));
#line 70 "src/jit_arm64.dasc"
}

// --- Bitwise ops ---

static void jit_emit_and(dasm_State **Dst, int dst, int left, int right) {
        //|  and Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 36, (dst), (left), (right));
#line 76 "src/jit_arm64.dasc"
}

static void jit_emit_or(dasm_State **Dst, int dst, int left, int right) {
        //|  orr Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 41, (dst), (left), (right));
#line 80 "src/jit_arm64.dasc"
}

static void jit_emit_xor(dasm_State **Dst, int dst, int left, int right) {
        //|  eor Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 46, (dst), (left), (right));
#line 84 "src/jit_arm64.dasc"
}

static void jit_emit_shl(dasm_State **Dst, int dst, int left, int right) {
        //|  lsl Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 51, (dst), (left), (right));
#line 88 "src/jit_arm64.dasc"
}

static void jit_emit_shr(dasm_State **Dst, int dst, int left, int right) {
        //|  asr Rx(dst), Rx(left), Rx(right)
        dasm_put(Dst, 56, (dst), (left), (right));
#line 92 "src/jit_arm64.dasc"
}

// --- Load immediate ---

static void jit_emit_load_imm(dasm_State **Dst, int dst, int64_t imm) {
        if (imm >= 0 && imm < 65536) {
                //|  movz Rx(dst), #imm
                dasm_put(Dst, 61, (dst), imm);
#line 99 "src/jit_arm64.dasc"
        } else if (imm >= -65536 && imm < 0) {
                //|  movn Rx(dst), #(~imm)
                dasm_put(Dst, 65, (dst), (~imm));
#line 101 "src/jit_arm64.dasc"
        } else {
                uint64_t u = (uint64_t)imm;
                //|  movz Rx(dst), #(u & 0xFFFF)
                dasm_put(Dst, 69, (dst), (u & 0xFFFF));
#line 104 "src/jit_arm64.dasc"
                if ((u >> 16) & 0xFFFF) {
                        //|  movk Rx(dst), #((u >> 16) & 0xFFFF), lsl #16
                        dasm_put(Dst, 73, (dst), ((u >> 16) & 0xFFFF));
#line 106 "src/jit_arm64.dasc"
                }
                if ((u >> 32) & 0xFFFF) {
                        //|  movk Rx(dst), #((u >> 32) & 0xFFFF), lsl #32
                        dasm_put(Dst, 77, (dst), ((u >> 32) & 0xFFFF));
#line 109 "src/jit_arm64.dasc"
                }
                if ((u >> 48) & 0xFFFF) {
                        //|  movk Rx(dst), #((u >> 48) & 0xFFFF), lsl #48
                        dasm_put(Dst, 81, (dst), ((u >> 48) & 0xFFFF));
#line 112 "src/jit_arm64.dasc"
                }
        }
}

// --- Move between registers ---

static void jit_emit_mov(dasm_State **Dst, int dst, int src) {
        if (dst != src) {
                //|  mov Rx(dst), Rx(src)
                dasm_put(Dst, 85, (dst), (src));
#line 121 "src/jit_arm64.dasc"
        }
}

// --- Comparisons (result is 0 or 1 in dst) ---

static void jit_emit_cmp_eq(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), eq
        dasm_put(Dst, 89, (left), (right), (dst));
#line 129 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_ne(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), ne
        dasm_put(Dst, 95, (left), (right), (dst));
#line 134 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_lt(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), lt
        dasm_put(Dst, 101, (left), (right), (dst));
#line 139 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_le(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), le
        dasm_put(Dst, 107, (left), (right), (dst));
#line 144 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_gt(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), gt
        dasm_put(Dst, 113, (left), (right), (dst));
#line 149 "src/jit_arm64.dasc"
}

static void jit_emit_cmp_ge(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rx(left), Rx(right)
        //|  cset Rx(dst), ge
        dasm_put(Dst, 119, (left), (right), (dst));
#line 154 "src/jit_arm64.dasc"
}

// --- Conditional branches ---

static void jit_emit_cbz(dasm_State **Dst, int reg, int label) {
        //|  cbz Rx(reg), =>label
        dasm_put(Dst, 125, (reg), label);
#line 160 "src/jit_arm64.dasc"
}

static void jit_emit_cbnz(dasm_State **Dst, int reg, int label) {
        //|  cbnz Rx(reg), =>label
        dasm_put(Dst, 129, (reg), label);
#line 164 "src/jit_arm64.dasc"
}

static void jit_emit_jump(dasm_State **Dst, int label) {
        //|  b =>label
        dasm_put(Dst, 133, label);
#line 168 "src/jit_arm64.dasc"
}

static void jit_emit_label(dasm_State **Dst, int label) {
        //|=>label:
        dasm_put(Dst, 136, label);
#line 172 "src/jit_arm64.dasc"
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
//   x21 = Value *args
//   x22 = Value *env
//   x23 = slot base pointer (== sp after slot allocation)
//
// Value slots live on the stack at [x23 + i*32].
// ============================================================================

static void jit_emit_gen_prologue(dasm_State **Dst, int slot_bytes) {
        //|->entry:
        //|  stp x29, x30, [sp, #-16]!
        //|  mov x29, sp
        //|  stp x19, x20, [sp, #-16]!
        //|  stp x21, x22, [sp, #-16]!
        //|  stp x23, x24, [sp, #-16]!
        dasm_put(Dst, 138);
#line 198 "src/jit_arm64.dasc"
        // Stash incoming args into callee-saved registers
        //|  mov x19, x0
        //|  mov x20, x1
        //|  mov x21, x2
        //|  mov x22, x3
        dasm_put(Dst, 145);
#line 203 "src/jit_arm64.dasc"
        // Allocate stack space for value slots
        if (slot_bytes > 0) {
                //|  sub sp, sp, #slot_bytes
                dasm_put(Dst, 150, slot_bytes);
#line 206 "src/jit_arm64.dasc"
        }
        //|  mov x23, sp
        dasm_put(Dst, 153);
#line 208 "src/jit_arm64.dasc"
}

static void jit_emit_gen_epilogue(dasm_State **Dst, int slot_bytes) {
        if (slot_bytes > 0) {
                //|  add sp, sp, #slot_bytes
                dasm_put(Dst, 155, slot_bytes);
#line 213 "src/jit_arm64.dasc"
        }
        //|  ldp x23, x24, [sp], #16
        //|  ldp x21, x22, [sp], #16
        //|  ldp x19, x20, [sp], #16
        //|  ldp x29, x30, [sp], #16
        //|  ret
        dasm_put(Dst, 158);
#line 219 "src/jit_arm64.dasc"
}

// --- Memory operations ---

// Load 64-bit from [base + offset]
static void jit_emit_ldr64(dasm_State **Dst, int dst, int base, int offset) {
        //|  ldr Rx(dst), [Rx(base), #offset]
        dasm_put(Dst, 164, (dst), (base), offset);
#line 226 "src/jit_arm64.dasc"
}

// Store 64-bit to [base + offset]
static void jit_emit_str64(dasm_State **Dst, int src, int base, int offset) {
        //|  str Rx(src), [Rx(base), #offset]
        dasm_put(Dst, 169, (src), (base), offset);
#line 231 "src/jit_arm64.dasc"
}

// Load byte from [base + offset]
static void jit_emit_ldrb(dasm_State **Dst, int dst, int base, int offset) {
        //|  ldrb Rw(dst), [Rx(base), #offset]
        dasm_put(Dst, 174, (dst), (base), offset);
#line 236 "src/jit_arm64.dasc"
}

// Store byte to [base + offset]
static void jit_emit_strb(dasm_State **Dst, int src, int base, int offset) {
        //|  strb Rw(src), [Rx(base), #offset]
        dasm_put(Dst, 179, (src), (base), offset);
#line 241 "src/jit_arm64.dasc"
}

// Store halfword (16-bit) to [base + offset]
static void jit_emit_strh(dasm_State **Dst, int src, int base, int offset) {
        //|  strh Rw(src), [Rx(base), #offset]
        dasm_put(Dst, 184, (src), (base), offset);
#line 246 "src/jit_arm64.dasc"
}

// Store 32-bit word to [base + offset]
static void jit_emit_str32(dasm_State **Dst, int src, int base, int offset) {
        //|  str Rw(src), [Rx(base), #offset]
        dasm_put(Dst, 189, (src), (base), offset);
#line 251 "src/jit_arm64.dasc"
}

// Load pair of 64-bit values from [base + offset]
static void jit_emit_ldp64(dasm_State **Dst, int r1, int r2, int base, int offset) {
        //|  ldp Rx(r1), Rx(r2), [Rx(base), #offset]
        dasm_put(Dst, 194, (r1), (r2), (base), offset);
#line 256 "src/jit_arm64.dasc"
}

// Store pair of 64-bit values to [base + offset]
static void jit_emit_stp64(dasm_State **Dst, int r1, int r2, int base, int offset) {
        //|  stp Rx(r1), Rx(r2), [Rx(base), #offset]
        dasm_put(Dst, 200, (r1), (r2), (base), offset);
#line 261 "src/jit_arm64.dasc"
}

// --- Add immediate ---
static void jit_emit_add_imm(dasm_State **Dst, int dst, int src, int imm) {
        if (imm == 0) {
                if (dst != src) {
                        //|  mov Rx(dst), Rx(src)
                        dasm_put(Dst, 206, (dst), (src));
#line 268 "src/jit_arm64.dasc"
                }
        } else {
                //|  add Rx(dst), Rx(src), #imm
                dasm_put(Dst, 210, (dst), (src), imm);
#line 271 "src/jit_arm64.dasc"
        }
}

// --- Indirect call ---
static void jit_emit_call_reg(dasm_State **Dst, int reg) {
        //|  blr Rx(reg)
        dasm_put(Dst, 215, (reg));
#line 277 "src/jit_arm64.dasc"
}

// --- Compare register with immediate ---
static void jit_emit_cmp_ri(dasm_State **Dst, int reg, int imm) {
        //|  cmp Rx(reg), #imm
        dasm_put(Dst, 218, (reg), imm);
#line 282 "src/jit_arm64.dasc"
}

// Compare 32-bit register with immediate (for int return values)
static void jit_emit_cmp_ri32(dasm_State **Dst, int reg, int imm) {
        //|  cmp Rw(reg), #imm
        dasm_put(Dst, 222, (reg), imm);
#line 287 "src/jit_arm64.dasc"
}

// --- Conditional branches (use after cmp_ri) ---
// ARM64 DynASM doesn't support b.cond syntax, so we use cset+cbz/cbnz.
// Call jit_emit_cmp_ri() first, then these:

static void jit_emit_branch_eq(dasm_State **Dst, int label) {
        // Branch if the cmp was equal: cset x16 to 1 if eq, then cbnz
        //|  cset x16, eq
        //|  cbnz x16, =>label
        dasm_put(Dst, 226, label);
#line 297 "src/jit_arm64.dasc"
}

static void jit_emit_branch_ne(dasm_State **Dst, int label) {
        //|  cset x16, ne
        //|  cbnz x16, =>label
        dasm_put(Dst, 230, label);
#line 302 "src/jit_arm64.dasc"
}

static void jit_emit_branch_lt(dasm_State **Dst, int label) {
        //|  cset x16, lt
        //|  cbnz x16, =>label
        dasm_put(Dst, 234, label);
#line 307 "src/jit_arm64.dasc"
}

static void jit_emit_branch_gt(dasm_State **Dst, int label) {
        //|  cset x16, gt
        //|  cbnz x16, =>label
        dasm_put(Dst, 238, label);
#line 312 "src/jit_arm64.dasc"
}

static void jit_emit_branch_le(dasm_State **Dst, int label) {
        //|  cset x16, le
        //|  cbnz x16, =>label
        dasm_put(Dst, 242, label);
#line 317 "src/jit_arm64.dasc"
}

static void jit_emit_branch_ge(dasm_State **Dst, int label) {
        //|  cset x16, ge
        //|  cbnz x16, =>label
        dasm_put(Dst, 246, label);
#line 322 "src/jit_arm64.dasc"
}

// Load 32-bit word from [base + offset]
static void jit_emit_ldr32(dasm_State **Dst, int dst, int base, int offset) {
        //|  ldr Rw(dst), [Rx(base), #offset]
        dasm_put(Dst, 250, (dst), (base), offset);
#line 327 "src/jit_arm64.dasc"
}
