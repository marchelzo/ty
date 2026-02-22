/*
** This file has been pre-processed with DynASM.
** https://luajit.org/dynasm.html
** DynASM version 1.5.0, DynASM x64 version 1.5.0
** DO NOT EDIT! The original file is in "src/jit_x64.dasc".
*/

#line 1 "src/jit_x64.dasc"
// jit_x64.dasc - DynASM x86-64 code generation templates for ty JIT
//
// Processed by: luajit LuaJIT/dynasm/dynasm.lua -o src/jit_x64.h src/jit_x64.dasc
//
// The generated jit_x64.h is included by src/jit.c
//

//|.arch x64
#if DASM_VERSION != 10500
#error "Version mismatch between DynASM and included encoding engine"
#endif
#line 9 "src/jit_x64.dasc"
//|.actionlist jit_actions
static const unsigned char jit_actions[599] = {
  248,10,255,195,255,72,1,192,240,131,240,35,255,72,137,192,240,131,240,35,
  72,1,192,240,131,240,35,255,72,41,192,240,131,240,35,255,72,137,192,240,131,
  240,35,72,41,192,240,131,240,35,255,72,15,175,192,240,132,240,36,255,72,137,
  192,240,131,240,35,72,15,175,192,240,132,240,36,255,72,137,192,240,131,72,
  153,72,252,247,252,248,240,35,255,72,137,192,240,35,255,72,137,208,240,35,
  255,72,137,192,240,131,240,35,255,72,252,247,216,240,35,255,72,33,192,240,
  131,240,35,255,72,137,192,240,131,240,35,72,33,192,240,131,240,35,255,72,
  9,192,240,131,240,35,255,72,137,192,240,131,240,35,72,9,192,240,131,240,35,
  255,72,49,192,240,131,240,35,255,72,137,192,240,131,240,35,72,49,192,240,
  131,240,35,255,72,137,193,240,131,72,137,192,240,131,240,35,72,211,224,240,
  35,255,72,137,193,240,131,72,137,192,240,131,240,35,72,211,252,248,240,35,
  255,64,49,192,240,131,240,51,255,72,199,192,240,35,237,255,72,184,240,34,
  237,237,255,72,57,192,240,131,240,35,64,15,148,208,240,36,72,15,182,192,240,
  132,240,36,255,72,57,192,240,131,240,35,64,15,149,208,240,36,72,15,182,192,
  240,132,240,36,255,72,57,192,240,131,240,35,64,15,156,208,240,36,72,15,182,
  192,240,132,240,36,255,72,57,192,240,131,240,35,64,15,158,208,240,36,72,15,
  182,192,240,132,240,36,255,72,57,192,240,131,240,35,64,15,159,208,240,36,
  72,15,182,192,240,132,240,36,255,72,57,192,240,131,240,35,64,15,157,208,240,
  36,72,15,182,192,240,132,240,36,255,72,133,192,240,131,240,35,15,132,245,
  255,72,133,192,240,131,240,35,15,133,245,255,252,233,245,255,249,255,248,
  10,85,72,137,229,83,65,84,65,85,65,86,65,87,255,72,131,252,236,8,255,73,137,
  252,252,73,137,252,245,73,137,214,73,137,207,255,72,129,252,236,239,255,72,
  137,227,255,72,129,196,239,255,72,131,196,8,65,95,65,94,65,93,65,92,91,93,
  195,255,72,139,128,253,240,131,240,3,233,255,72,137,128,253,240,131,240,3,
  233,255,64,15,182,128,253,240,132,240,20,233,255,64,136,128,253,240,131,240,
  3,233,255,102,64,137,128,253,240,131,240,19,233,255,64,139,128,253,240,131,
  240,19,233,255,72,139,128,253,240,131,240,3,233,72,139,128,253,240,131,240,
  3,233,255,72,137,128,253,240,131,240,3,233,72,137,128,253,240,131,240,3,233,
  255,72,141,128,253,240,131,240,3,233,255,64,252,255,208,240,43,255,72,129,
  252,248,240,35,239,255
};

#line 10 "src/jit_x64.dasc"
//|.section code
#define DASM_SECTION_CODE	0
#define DASM_MAXSECTION		1
#line 11 "src/jit_x64.dasc"
//|.globals JIT_GLOB_
enum {
  JIT_GLOB_entry,
  JIT_GLOB__MAX
};
#line 12 "src/jit_x64.dasc"

// ============================================================================
// INT MODE: Pure integer functions
//
// x86-64 System V calling convention:
//   intmax_t fn(intmax_t a0, intmax_t a1, intmax_t a2, intmax_t a3)
//   Arguments: rdi, rsi, rdx, rcx
//   Return: rax
//   Scratch: r8-r11 (caller-saved)
// ============================================================================

//|.define ARG0, rdi
//|.define ARG1, rsi
//|.define ARG2, rdx
//|.define ARG3, rcx
//|.define RET,  rax

static void jit_emit_prologue(dasm_State **Dst) {
        //|->entry:
        dasm_put(Dst, 0);
#line 31 "src/jit_x64.dasc"
}

static void jit_emit_epilogue(dasm_State **Dst) {
        //|  ret
        dasm_put(Dst, 3);
#line 35 "src/jit_x64.dasc"
}

// --- Integer arithmetic ---

static void jit_emit_add(dasm_State **Dst, int dst, int left, int right) {
        if (dst == left) {
                //|  add Rq(dst), Rq(right)
                dasm_put(Dst, 5, (right), (dst));
#line 42 "src/jit_x64.dasc"
        } else if (dst == right) {
                //|  add Rq(dst), Rq(left)
                dasm_put(Dst, 5, (left), (dst));
#line 44 "src/jit_x64.dasc"
        } else {
                //|  mov Rq(dst), Rq(left)
                //|  add Rq(dst), Rq(right)
                dasm_put(Dst, 13, (left), (dst), (right), (dst));
#line 47 "src/jit_x64.dasc"
        }
}

static void jit_emit_sub(dasm_State **Dst, int dst, int left, int right) {
        if (dst == left) {
                //|  sub Rq(dst), Rq(right)
                dasm_put(Dst, 28, (right), (dst));
#line 53 "src/jit_x64.dasc"
        } else {
                //|  mov Rq(dst), Rq(left)
                //|  sub Rq(dst), Rq(right)
                dasm_put(Dst, 36, (left), (dst), (right), (dst));
#line 56 "src/jit_x64.dasc"
        }
}

static void jit_emit_mul(dasm_State **Dst, int dst, int left, int right) {
        if (dst == left) {
                //|  imul Rq(dst), Rq(right)
                dasm_put(Dst, 51, (dst), (right));
#line 62 "src/jit_x64.dasc"
        } else if (dst == right) {
                //|  imul Rq(dst), Rq(left)
                dasm_put(Dst, 51, (dst), (left));
#line 64 "src/jit_x64.dasc"
        } else {
                //|  mov Rq(dst), Rq(left)
                //|  imul Rq(dst), Rq(right)
                dasm_put(Dst, 60, (left), (dst), (dst), (right));
#line 67 "src/jit_x64.dasc"
        }
}

static void jit_emit_sdiv(dasm_State **Dst, int dst, int left, int right) {
        //|  mov rax, Rq(left)
        //|  cqo
        //|  idiv Rq(right)
        dasm_put(Dst, 76, (left), (right));
#line 74 "src/jit_x64.dasc"
        if (dst != 0) {
                //|  mov Rq(dst), rax
                dasm_put(Dst, 91, (dst));
#line 76 "src/jit_x64.dasc"
        }
}

static void jit_emit_mod(dasm_State **Dst, int dst, int left, int right) {
        //|  mov rax, Rq(left)
        //|  cqo
        //|  idiv Rq(right)
        dasm_put(Dst, 76, (left), (right));
#line 83 "src/jit_x64.dasc"
        if (dst != 2) {
                //|  mov Rq(dst), rdx
                dasm_put(Dst, 97, (dst));
#line 85 "src/jit_x64.dasc"
        }
}

static void jit_emit_neg(dasm_State **Dst, int dst, int src) {
        if (dst != src) {
                //|  mov Rq(dst), Rq(src)
                dasm_put(Dst, 103, (src), (dst));
#line 91 "src/jit_x64.dasc"
        }
        //|  neg Rq(dst)
        dasm_put(Dst, 111, (dst));
#line 93 "src/jit_x64.dasc"
}

// --- Bitwise ops ---

static void jit_emit_and(dasm_State **Dst, int dst, int left, int right) {
        if (dst == left) {
                //|  and Rq(dst), Rq(right)
                dasm_put(Dst, 118, (right), (dst));
#line 100 "src/jit_x64.dasc"
        } else {
                //|  mov Rq(dst), Rq(left)
                //|  and Rq(dst), Rq(right)
                dasm_put(Dst, 126, (left), (dst), (right), (dst));
#line 103 "src/jit_x64.dasc"
        }
}

static void jit_emit_or(dasm_State **Dst, int dst, int left, int right) {
        if (dst == left) {
                //|  or Rq(dst), Rq(right)
                dasm_put(Dst, 141, (right), (dst));
#line 109 "src/jit_x64.dasc"
        } else {
                //|  mov Rq(dst), Rq(left)
                //|  or Rq(dst), Rq(right)
                dasm_put(Dst, 149, (left), (dst), (right), (dst));
#line 112 "src/jit_x64.dasc"
        }
}

static void jit_emit_xor(dasm_State **Dst, int dst, int left, int right) {
        if (dst == left) {
                //|  xor Rq(dst), Rq(right)
                dasm_put(Dst, 164, (right), (dst));
#line 118 "src/jit_x64.dasc"
        } else {
                //|  mov Rq(dst), Rq(left)
                //|  xor Rq(dst), Rq(right)
                dasm_put(Dst, 172, (left), (dst), (right), (dst));
#line 121 "src/jit_x64.dasc"
        }
}

static void jit_emit_shl(dasm_State **Dst, int dst, int left, int right) {
        //|  mov rcx, Rq(right)
        //|  mov Rq(dst), Rq(left)
        //|  shl Rq(dst), cl
        dasm_put(Dst, 187, (right), (left), (dst), (dst));
#line 128 "src/jit_x64.dasc"
}

static void jit_emit_shr(dasm_State **Dst, int dst, int left, int right) {
        //|  mov rcx, Rq(right)
        //|  mov Rq(dst), Rq(left)
        //|  sar Rq(dst), cl
        dasm_put(Dst, 205, (right), (left), (dst), (dst));
#line 134 "src/jit_x64.dasc"
}

// --- Load immediate ---

static void jit_emit_load_imm(dasm_State **Dst, int dst, int64_t imm) {
        if (imm == 0) {
                //|  xor Rd(dst), Rd(dst)
                dasm_put(Dst, 224, (dst), (dst));
#line 141 "src/jit_x64.dasc"
        } else if (imm >= INT32_MIN && imm <= INT32_MAX) {
                //|  mov Rq(dst), imm
                dasm_put(Dst, 232, (dst), imm);
#line 143 "src/jit_x64.dasc"
        } else {
                //|  mov64 Rq(dst), imm
                dasm_put(Dst, 239, (dst), (unsigned int)(imm), (unsigned int)((imm)>>32));
#line 145 "src/jit_x64.dasc"
        }
}

// --- Move between registers ---

static void jit_emit_mov(dasm_State **Dst, int dst, int src) {
        if (dst != src) {
                //|  mov Rq(dst), Rq(src)
                dasm_put(Dst, 103, (src), (dst));
#line 153 "src/jit_x64.dasc"
        }
}

// --- Comparisons ---

static void jit_emit_cmp_eq(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rq(left), Rq(right)
        //|  sete Rb(dst)
        //|  movzx Rq(dst), Rb(dst)
        dasm_put(Dst, 246, (right), (left), (dst), (dst), (dst));
#line 162 "src/jit_x64.dasc"
}

static void jit_emit_cmp_ne(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rq(left), Rq(right)
        //|  setne Rb(dst)
        //|  movzx Rq(dst), Rb(dst)
        dasm_put(Dst, 268, (right), (left), (dst), (dst), (dst));
#line 168 "src/jit_x64.dasc"
}

static void jit_emit_cmp_lt(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rq(left), Rq(right)
        //|  setl Rb(dst)
        //|  movzx Rq(dst), Rb(dst)
        dasm_put(Dst, 290, (right), (left), (dst), (dst), (dst));
#line 174 "src/jit_x64.dasc"
}

static void jit_emit_cmp_le(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rq(left), Rq(right)
        //|  setle Rb(dst)
        //|  movzx Rq(dst), Rb(dst)
        dasm_put(Dst, 312, (right), (left), (dst), (dst), (dst));
#line 180 "src/jit_x64.dasc"
}

static void jit_emit_cmp_gt(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rq(left), Rq(right)
        //|  setg Rb(dst)
        //|  movzx Rq(dst), Rb(dst)
        dasm_put(Dst, 334, (right), (left), (dst), (dst), (dst));
#line 186 "src/jit_x64.dasc"
}

static void jit_emit_cmp_ge(dasm_State **Dst, int dst, int left, int right) {
        //|  cmp Rq(left), Rq(right)
        //|  setge Rb(dst)
        //|  movzx Rq(dst), Rb(dst)
        dasm_put(Dst, 356, (right), (left), (dst), (dst), (dst));
#line 192 "src/jit_x64.dasc"
}

// --- Conditional branches ---

static void jit_emit_cbz(dasm_State **Dst, int reg, int label) {
        //|  test Rq(reg), Rq(reg)
        //|  jz =>label
        dasm_put(Dst, 378, (reg), (reg), label);
#line 199 "src/jit_x64.dasc"
}

static void jit_emit_cbnz(dasm_State **Dst, int reg, int label) {
        //|  test Rq(reg), Rq(reg)
        //|  jnz =>label
        dasm_put(Dst, 389, (reg), (reg), label);
#line 204 "src/jit_x64.dasc"
}

static void jit_emit_jump(dasm_State **Dst, int label) {
        //|  jmp =>label
        dasm_put(Dst, 400, label);
#line 208 "src/jit_x64.dasc"
}

static void jit_emit_label(dasm_State **Dst, int label) {
        //|=>label:
        dasm_put(Dst, 404, label);
#line 212 "src/jit_x64.dasc"
}

// ============================================================================
// GENERIC MODE: Value-typed functions with C helper calls
//
// Calling convention:
//   void fn(Ty *ty, Value *result, Value *args, Value *env)
//   rdi=ty, rsi=result, rdx=args, rcx=env
//
// Callee-saved register assignments:
//   r12 = Ty *ty
//   r13 = Value *result
//   r14 = Value *args
//   r15 = Value *env
//   rbx = slot base pointer (== rsp after slot allocation)
// ============================================================================

static void jit_emit_gen_prologue(dasm_State **Dst, int slot_bytes) {
        //|->entry:
        //|  push rbp
        //|  mov rbp, rsp
        //|  push rbx
        //|  push r12
        //|  push r13
        //|  push r14
        //|  push r15
        dasm_put(Dst, 406);
#line 238 "src/jit_x64.dasc"
        // 5 pushes + rbp = 6 * 8 = 48 bytes. RSP was 16n-8 on entry,
        // now 16n-56. Need 8 bytes padding for alignment.
        //|  sub rsp, 8
        dasm_put(Dst, 422);
#line 241 "src/jit_x64.dasc"
        // Stash args
        //|  mov r12, rdi
        //|  mov r13, rsi
        //|  mov r14, rdx
        //|  mov r15, rcx
        dasm_put(Dst, 428);
#line 246 "src/jit_x64.dasc"
        // Allocate value slots (slot_bytes must be multiple of 16)
        if (slot_bytes > 0) {
                //|  sub rsp, slot_bytes
                dasm_put(Dst, 443, slot_bytes);
#line 249 "src/jit_x64.dasc"
        }
        //|  mov rbx, rsp
        dasm_put(Dst, 449);
#line 251 "src/jit_x64.dasc"
}

static void jit_emit_gen_epilogue(dasm_State **Dst, int slot_bytes) {
        if (slot_bytes > 0) {
                //|  add rsp, slot_bytes
                dasm_put(Dst, 453, slot_bytes);
#line 256 "src/jit_x64.dasc"
        }
        //|  add rsp, 8
        //|  pop r15
        //|  pop r14
        //|  pop r13
        //|  pop r12
        //|  pop rbx
        //|  pop rbp
        //|  ret
        dasm_put(Dst, 458);
#line 265 "src/jit_x64.dasc"
}

// --- Memory operations ---

static void jit_emit_ldr64(dasm_State **Dst, int dst, int base, int offset) {
        //|  mov Rq(dst), [Rq(base)+offset]
        dasm_put(Dst, 474, (dst), (base), offset);
#line 271 "src/jit_x64.dasc"
}

static void jit_emit_str64(dasm_State **Dst, int src, int base, int offset) {
        //|  mov [Rq(base)+offset], Rq(src)
        dasm_put(Dst, 484, (src), (base), offset);
#line 275 "src/jit_x64.dasc"
}

static void jit_emit_ldrb(dasm_State **Dst, int dst, int base, int offset) {
        //|  movzx Rd(dst), byte [Rq(base)+offset]
        dasm_put(Dst, 494, (dst), (base), offset);
#line 279 "src/jit_x64.dasc"
}

static void jit_emit_strb(dasm_State **Dst, int src, int base, int offset) {
        //|  mov byte [Rq(base)+offset], Rb(src)
        dasm_put(Dst, 505, (src), (base), offset);
#line 283 "src/jit_x64.dasc"
}

static void jit_emit_strh(dasm_State **Dst, int src, int base, int offset) {
        //|  mov word [Rq(base)+offset], Rw(src)
        dasm_put(Dst, 515, (src), (base), offset);
#line 287 "src/jit_x64.dasc"
}

static void jit_emit_str32(dasm_State **Dst, int src, int base, int offset) {
        //|  mov dword [Rq(base)+offset], Rd(src)
        dasm_put(Dst, 516, (src), (base), offset);
#line 291 "src/jit_x64.dasc"
}

static void jit_emit_ldr32(dasm_State **Dst, int dst, int base, int offset) {
        //|  mov Rd(dst), dword [Rq(base)+offset]
        dasm_put(Dst, 526, (dst), (base), offset);
#line 295 "src/jit_x64.dasc"
}

// Load/store pairs (just two sequential loads/stores on x64)
static void jit_emit_ldp64(dasm_State **Dst, int r1, int r2, int base, int offset) {
        //|  mov Rq(r1), [Rq(base)+offset]
        //|  mov Rq(r2), [Rq(base)+(offset+8)]
        dasm_put(Dst, 536, (@q1), (base), offset, (@q2), (base), (offset+8));
#line 301 "src/jit_x64.dasc"
}

static void jit_emit_stp64(dasm_State **Dst, int r1, int r2, int base, int offset) {
        //|  mov [Rq(base)+offset], Rq(r1)
        //|  mov [Rq(base)+(offset+8)], Rq(r2)
        dasm_put(Dst, 555, (@q1), (base), offset, (@q2), (base), (offset+8));
#line 306 "src/jit_x64.dasc"
}

// --- Add immediate ---
static void jit_emit_add_imm(dasm_State **Dst, int dst, int src, int imm) {
        if (imm == 0) {
                if (dst != src) {
                        //|  mov Rq(dst), Rq(src)
                        dasm_put(Dst, 103, (src), (dst));
#line 313 "src/jit_x64.dasc"
                }
        } else {
                //|  lea Rq(dst), [Rq(src)+imm]
                dasm_put(Dst, 574, (dst), (src), imm);
#line 316 "src/jit_x64.dasc"
        }
}

// --- Indirect call ---
static void jit_emit_call_reg(dasm_State **Dst, int reg) {
        //|  call Rq(reg)
        dasm_put(Dst, 584, (reg));
#line 322 "src/jit_x64.dasc"
}

// --- Compare register with immediate ---
static void jit_emit_cmp_ri(dasm_State **Dst, int reg, int imm) {
        //|  cmp Rq(reg), imm
        dasm_put(Dst, 591, (reg), imm);
#line 327 "src/jit_x64.dasc"
}

// --- Conditional branches (use after cmp) ---
static void jit_emit_branch_eq(dasm_State **Dst, int label) {
        //|  je =>label
        dasm_put(Dst, 385, label);
#line 332 "src/jit_x64.dasc"
}

static void jit_emit_branch_ne(dasm_State **Dst, int label) {
        //|  jne =>label
        dasm_put(Dst, 396, label);
#line 336 "src/jit_x64.dasc"
}
