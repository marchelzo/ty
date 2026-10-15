#ifndef LIR_H_INCLUDED
#define LIR_H_INCLUDED

#include <stdio.h>
#include <signal.h>

#include "defs.h"

typedef struct lir Lir;
typedef struct lir_code LirCode;
typedef struct lir_alloc LirAlloc;
typedef struct lir_target LirTarget;

typedef u32 LirReg;
typedef u32 LirLabel;

extern char LirRefRoot;

#define LIR_NONE UINT32_MAX
#define LIR_MAX_OPERANDS 6
#define LIR_MAX_PHYS 32
#define LIR_MAX_PINS 8
#define LIR_MAX_SWITCH 65536
#define LIR_PHYS_NONE UINT8_MAX

typedef enum lir_class {
        LIR_I32,
        LIR_I64,
        LIR_F32,
        LIR_F64,
        LIR_PTR,
        LIR_REF,
        LIR_CLASS_COUNT
} LirClass;

typedef enum lir_type {
        LIR_VOID,
        LIR_TYPE_I8,
        LIR_TYPE_U8,
        LIR_TYPE_I16,
        LIR_TYPE_U16,
        LIR_TYPE_I32,
        LIR_TYPE_U32,
        LIR_TYPE_I64,
        LIR_TYPE_U64,
        LIR_TYPE_F32,
        LIR_TYPE_F64,
        LIR_TYPE_BOOL,
        LIR_TYPE_PTR,
        LIR_TYPE_REF,
        LIR_TYPE_VAL,
        LIR_TYPE_COUNT
} LirType;

typedef enum lir_cc {
        LIR_EQ, LIR_NE, LIR_LT, LIR_LE, LIR_GT, LIR_GE,
        LIR_ULT, LIR_ULE, LIR_UGT, LIR_UGE,
        LIR_FEQ, LIR_FNE, LIR_FLT, LIR_FLE, LIR_FGT, LIR_FGE, LIR_FUN,
        LIR_CC_COUNT
} LirCC;

typedef enum lir_mode {
        LIR_MODE_AUTO,
        LIR_MODE_DETACHED,
        LIR_MODE_ATTACHED
} LirMode;

typedef enum lir_pin {
        LIR_PIN_0, LIR_PIN_1, LIR_PIN_2, LIR_PIN_3,
        LIR_PIN_4, LIR_PIN_5, LIR_PIN_6, LIR_PIN_7
} LirPin;

typedef enum lir_call_flags {
        LIR_MAY_GC        = 1 << 0,
        LIR_MAY_THROW     = 1 << 1,
        LIR_RETURNS_TWICE = 1 << 2,
        LIR_NORETURN      = 1 << 3,
        LIR_CALL_SITE     = 1 << 4,
        LIR_READS_NO_LOCALS = 1 << 5,
        LIR_WRITES_LOCALS = 1 << 6
} LirCallFlags;

typedef struct lir_sig {
        LirType        ret;
        LirType const *params;
        u32            nparams;
        u32            nfixed;
        bool           variadic;
} LirSig;

typedef struct lir_mem {
        LirReg base;
        LirReg index;
        u8     scale;
        i32    disp;
} LirMem;

typedef struct lir_span {
        u32 source;
        u32 start;
        u32 end;
} LirSpan;

typedef enum lir_operand_kind {
        LIR_OPERAND_NONE,
        LIR_OPERAND_REG,
        LIR_OPERAND_IMM,
        LIR_OPERAND_FIMM,
        LIR_OPERAND_MEM,
        LIR_OPERAND_LABEL,
        LIR_OPERAND_CC,
        LIR_OPERAND_CONST,
        LIR_OPERAND_REFCONST,
        LIR_OPERAND_CODE,
        LIR_OPERAND_HELPER,
        LIR_OPERAND_VSLOT,
        LIR_HOLE_IMM,
        LIR_HOLE_FIMM,
        LIR_HOLE_PTR,
        LIR_HOLE_CONST,
        LIR_HOLE_CALLEE
} LirOperandKind;

typedef struct lir_helper {
        char const *name;
        void       *address;
        LirSig      sig;
        u32         flags;
} LirHelper;

typedef struct lir_operand {
        LirOperandKind kind;
        union {
                LirReg           reg;
                i64              imm;
                double           fimm;
                LirMem           mem;
                LirLabel         label;
                LirCC            cc;
                u32              index;
                LirCode         *code;
                LirHelper const *helper;
        };
} LirOpnd;

typedef enum lir_form {
        LIR_FORM_MOV,
        LIR_FORM_LI,
        LIR_FORM_FLI,
        LIR_FORM_LEA,
        LIR_FORM_IBINARY,
        LIR_FORM_IUNARY,
        LIR_FORM_CHECKED,
        LIR_FORM_FBINARY,
        LIR_FORM_FUNARY,
        LIR_FORM_FMA,
        LIR_FORM_I2F,
        LIR_FORM_F2I,
        LIR_FORM_FEXT,
        LIR_FORM_FTRUNC,
        LIR_FORM_BITCAST,
        LIR_FORM_LD,
        LIR_FORM_ST,
        LIR_FORM_SETCC,
        LIR_FORM_FSETCC,
        LIR_FORM_SELECT,
        LIR_FORM_FSELECT,
        LIR_FORM_BR,
        LIR_FORM_FBR,
        LIR_FORM_BRZ,
        LIR_FORM_JMP,
        LIR_FORM_SWITCH,
        LIR_FORM_RET,
        LIR_FORM_CALL,
        LIR_FORM_TAILCALL,
        LIR_FORM_CAS,
        LIR_FORM_ATOMIC,
        LIR_FORM_FENCE,
        LIR_FORM_ALLOCA,
        LIR_FORM_POLL,
        LIR_FORM_SITE,
        LIR_FORM_ENTRY,
        LIR_FORM_RAW,
        LIR_FORM_COPY
} LirForm;

#define LIR_OPS(X) \
        X(MOV,      MOV,      VOID, 1, "d,v") \
        X(LI,       LI,       VOID, 1, "d,imm") \
        X(FLI,      FLI,      VOID, 1, "d,fimm") \
        X(LEA,      LEA,      PTR,  1, "d,mem") \
        X(ADD,      IBINARY,  VOID, 2, "d,a,b") \
        X(SUB,      IBINARY,  VOID, 2, "d,a,b") \
        X(MUL,      IBINARY,  VOID, 2, "d,a,b") \
        X(MULHS,    IBINARY,  VOID, 2, "d,a,b") \
        X(MULHU,    IBINARY,  VOID, 2, "d,a,b") \
        X(SDIV,     IBINARY,  VOID, 2, "d,a,b") \
        X(UDIV,     IBINARY,  VOID, 2, "d,a,b") \
        X(SREM,     IBINARY,  VOID, 2, "d,a,b") \
        X(UREM,     IBINARY,  VOID, 2, "d,a,b") \
        X(AND,      IBINARY,  VOID, 2, "d,a,b") \
        X(OR,       IBINARY,  VOID, 2, "d,a,b") \
        X(XOR,      IBINARY,  VOID, 2, "d,a,b") \
        X(SHL,      IBINARY,  VOID, 2, "d,a,b") \
        X(SHR,      IBINARY,  VOID, 2, "d,a,b") \
        X(SAR,      IBINARY,  VOID, 2, "d,a,b") \
        X(ROTR,     IBINARY,  VOID, 2, "d,a,b") \
        X(NEG,      IUNARY,   VOID, 1, "d,a") \
        X(NOT,      IUNARY,   VOID, 1, "d,a") \
        X(CLZ,      IUNARY,   VOID, 1, "d,a") \
        X(CTZ,      IUNARY,   VOID, 1, "d,a") \
        X(POPCNT,   IUNARY,   VOID, 1, "d,a") \
        X(BSWAP,    IUNARY,   VOID, 1, "d,a") \
        X(SEXT8,    IUNARY,   VOID, 1, "d,a") \
        X(SEXT16,   IUNARY,   VOID, 1, "d,a") \
        X(SEXT32,   IUNARY,   VOID, 1, "d,a") \
        X(ZEXT8,    IUNARY,   VOID, 1, "d,a") \
        X(ZEXT16,   IUNARY,   VOID, 1, "d,a") \
        X(ZEXT32,   IUNARY,   VOID, 1, "d,a") \
        X(ADDO,     CHECKED,  VOID, 3, "d,a,b,L") \
        X(SUBO,     CHECKED,  VOID, 3, "d,a,b,L") \
        X(MULO,     CHECKED,  VOID, 3, "d,a,b,L") \
        X(FADD,     FBINARY,  VOID, 2, "d,a,b") \
        X(FSUB,     FBINARY,  VOID, 2, "d,a,b") \
        X(FMUL,     FBINARY,  VOID, 2, "d,a,b") \
        X(FDIV,     FBINARY,  VOID, 2, "d,a,b") \
        X(FMIN,     FBINARY,  VOID, 2, "d,a,b") \
        X(FMAX,     FBINARY,  VOID, 2, "d,a,b") \
        X(FSQRT,    FUNARY,   VOID, 1, "d,a") \
        X(FABS,     FUNARY,   VOID, 1, "d,a") \
        X(FNEG,     FUNARY,   VOID, 1, "d,a") \
        X(FMA,      FMA,      VOID, 3, "d,a,b,c") \
        X(I2F,      I2F,      VOID, 1, "d,a") \
        X(U2F,      I2F,      VOID, 1, "d,a") \
        X(F2I,      F2I,      VOID, 1, "d,a") \
        X(FEXT,     FEXT,     F64,  1, "d,a") \
        X(FTRUNC,   FTRUNC,   F32,  1, "d,a") \
        X(BITCAST,  BITCAST,  VOID, 1, "d,a") \
        X(LD_I8,    LD,       I8,   1, "d,mem") \
        X(LD_U8,    LD,       U8,   1, "d,mem") \
        X(LD_I16,   LD,       I16,  1, "d,mem") \
        X(LD_U16,   LD,       U16,  1, "d,mem") \
        X(LD_I32,   LD,       I32,  1, "d,mem") \
        X(LD_U32,   LD,       U32,  1, "d,mem") \
        X(LD_I64,   LD,       I64,  1, "d,mem") \
        X(LD_F32,   LD,       F32,  1, "d,mem") \
        X(LD_F64,   LD,       F64,  1, "d,mem") \
        X(ST8,      ST,       I8,   2, "mem,a") \
        X(ST16,     ST,       I16,  2, "mem,a") \
        X(ST32,     ST,       I32,  2, "mem,a") \
        X(ST64,     ST,       I64,  2, "mem,a") \
        X(ST_F32,   ST,       F32,  2, "mem,a") \
        X(ST_F64,   ST,       F64,  2, "mem,a") \
        X(SETCC,    SETCC,    VOID, 3, "d,cc,a,b") \
        X(FSETCC,   FSETCC,   VOID, 3, "d,fcc,a,b") \
        X(SELECT,   SELECT,   VOID, 5, "d,cc,a,b,x,y") \
        X(FSELECT,  FSELECT,  VOID, 5, "d,fcc,a,b,x,y") \
        X(BR,       BR,       VOID, 4, "cc,a,b,L") \
        X(FBR,      FBR,      VOID, 4, "fcc,a,b,L") \
        X(BRZ,      BRZ,      VOID, 2, "a,L") \
        X(BRNZ,     BRZ,      VOID, 2, "a,L") \
        X(JMP,      JMP,      VOID, 1, "L") \
        X(SWITCH,   SWITCH,   VOID, 2, "a,Ldefault;labels") \
        X(RET,      RET,      VOID, 0, "[a]") \
        X(CALL,     CALL,     VOID, 1, "[d],target;args,sig,flags") \
        X(TAILCALL, TAILCALL, VOID, 1, "target;args,sig,flags") \
        X(CAS,      CAS,      VOID, 3, "d,mem,expected,new") \
        X(XADD,     ATOMIC,   VOID, 2, "d,mem,a") \
        X(XCHG,     ATOMIC,   VOID, 2, "d,mem,a") \
        X(FENCE,    FENCE,    VOID, 0, "") \
        X(ALLOCA,   ALLOCA,   PTR,  2, "d,size,align") \
        X(POLL,     POLL,     VOID, 1, "[ty,top,info],Ldeopt") \
        X(SITE,     SITE,     VOID, 1, "tag") \
        X(ENTRY,    ENTRY,    VOID, 1, "L") \
        X(RAW,      RAW,      VOID, 0, ";bytes,inputs,outputs,clobbers") \
        X(COPY32,   COPY,     VOID, 2, "mem,mem")

typedef enum lir_op {
#define LIR_ENUM(name, form, type, argc, signature) LIR_##name,
        LIR_OPS(LIR_ENUM)
#undef LIR_ENUM
        LIR_OP_COUNT
} LirOp;

typedef struct lir_op_info {
        char const *name;
        LirForm     form;
        LirType     type;
        u8          argc;
        char const *signature;
} LirOpInfo;

extern LirOpInfo const LirOps[LIR_OP_COUNT];

typedef struct lir_raw_binding {
        u8     phys;
        LirReg reg;
} LirRawBinding;

typedef struct lir_raw {
        u32 const           *arm64;
        u32                  narm64;
        u8 const            *x64;
        u32                  nx64;
        LirRawBinding const *in;
        u32                  nin;
        LirRawBinding const *out;
        u32                  nout;
        u64                  gpr_clobber;
        u64                  fpr_clobber;
} LirRaw;

typedef struct lir_inst {
        LirOp     op;
        LirReg    dst;
        LirOpnd   args[LIR_MAX_OPERANDS];
        u8        nargs;
        u32       flags;
        u32       tag;
        LirSpan   span;
        LirSig    sig;
        LirOpnd  *call_args;
        u32       ncall_args;
        LirLabel *targets;
        u32       ntargets;
        LirRaw    raw;
} LirInst;

typedef struct lir_reg_info {
        LirClass cls;
        u32      param;
        u32      pin;
} LirRegInfo;

typedef struct lir_label_info {
        u32  pos;
        bool entry;
} LirLabelInfo;

typedef enum lir_error_kind {
        LIR_ERROR_NONE,
        LIR_ERROR_MEMORY,
        LIR_ERROR_SIGNATURE,
        LIR_ERROR_OPERAND,
        LIR_ERROR_CLASS,
        LIR_ERROR_LABEL,
        LIR_ERROR_UNDEFINED,
        LIR_ERROR_RETURN,
        LIR_ERROR_ENTRY,
        LIR_ERROR_RETURNS_TWICE,
        LIR_ERROR_MODE,
        LIR_ERROR_ENCODING,
        LIR_ERROR_TARGET
} LirErrorKind;

typedef struct lir_error {
        LirErrorKind kind;
        u32          op;
        LirSpan      span;
        char         message[192];
} LirError;

typedef struct lir_block {
        u32  first;
        u32  end;
        u32 *succ;
        u32  nsucc;
        u64 *use;
        u64 *def;
        u64 *live_in;
        u64 *live_out;
        bool reachable;
        bool entry;
} LirBlock;

typedef struct lir_cfg {
        LirBlock *blocks;
        u32       nblocks;
        u32      *block_at;
        u32       nwords;
        u32      *global;
        u32      *globals;
        u32       nglobals;
        u64      *sets;
        u32      *edges;
} LirCFG;

struct lir {
        char         *name;
        LirSig        sig;
        LirMode       mode;
        LirMode       resolved_mode;
        LirReg       *params;
        LirReg        pins[LIR_MAX_PINS];
        LirRegInfo   *regs;
        u32           nregs;
        u32           reg_capacity;
        LirLabelInfo *labels;
        u32           nlabels;
        u32           label_capacity;
        LirInst      *insts;
        u32           ninsts;
        u32           inst_capacity;
        Value        *roots;
        u32           nroots;
        u32           root_capacity;
        u32           nvslots;
        u32           pc_param;
        u32           ty_param;
        u8            stable_pins;
        bool          trusted;
        u8            stack_pins;
        LirError      error;
};

typedef enum lir_arch {
        LIR_ARCH_NONE,
        LIR_ARCH_ARM64,
        LIR_ARCH_X64
} LirArch;

typedef enum lir_abi {
        LIR_ABI_SYSV,
        LIR_ABI_AAPCS64,
        LIR_ABI_APPLE_ARM64
} LirABI;

typedef struct lir_reg_pool {
        u64 available;
        u64 callee_saved;
        u8  args[LIR_MAX_PHYS];
        u8  nargs;
        u8  ret;
        u8  scratch[2];
        u8  nscratch;
} LirRegPool;

typedef struct lir_constraint {
        u32    op;
        LirReg reg;
        u8     phys;
        bool   output;
        bool   fpr;
        LirReg tied;
} LirConstraint;

typedef struct lir_range {
        u32 start;
        u32 end;
} LirRange;

typedef struct lir_interval {
        LirReg    reg;
        LirRange *ranges;
        u32       nranges;
        u32      *uses;
        u32       nuses;
        u32       spill;
        u32       call_save;
        u32       root_slot;
        u8        phys;
        bool      spilled;
        bool      crosses_call;
} LirInterval;

typedef enum lir_move_kind {
        LIR_MOVE_COPY,
        LIR_MOVE_ROOT
} LirMoveKind;

typedef enum lir_move_phase {
        LIR_MOVE_BEFORE,
        LIR_MOVE_AFTER
} LirMovePhase;

typedef struct lir_move {
        u32          op;
        LirMoveKind  kind;
        LirMovePhase phase;
        LirReg       from;
        LirReg       to;
        u32          from_slot;
        u32          to_slot;
        u8           from_phys;
        u8           to_phys;
        LirClass     cls;
        bool         from_gpr;
        bool         to_gpr;
} LirMove;

struct lir_alloc {
        LirInterval   *intervals;
        u32            nintervals;
        u32            spill_size;
        u32            frame_size;
        u32            frame_align;
        u64            saved_gpr;
        u64            saved_fpr;
        LirMove       *moves;
        u32            nmoves;
        u32            nvslots;
        u32           *alloca_offsets;
        LirConstraint *constraints;
        u32            nconstraints;
        LirRange      *range_pool;
        u32           *use_pool;
};

typedef struct lir_site {
        u32 pc;
        u32 tag;
} LirSite;

typedef struct lir_image {
        u32 size;
        u32 table;
        u32 nsites;
        u32 nresume;
} LirImage;

typedef struct lir_entry_info {
        LirLabel label;
        u32      offset;
} LirEntryInfo;

typedef void JitEntry(Ty *, Value *, Value const *, i32);

struct lir_code {
        void         *body;
        JitEntry     *entry;
        usize         size;
        void         *allocation;
        void         *literal_pool;
        usize         literal_size;
        Value        *roots;
        u32           nroots;
        LirSite      *sites;
        u32           nsites;
        LirEntryInfo *entries;
        u32           nentries;
        char         *name;
        LirSig        sig;
        LirMode       mode;
        u32           nvslots;
        Lir          *lir;
        LirCode      *entry_code;
        void         *interp_state;
        u32           entry_body_slots;
        u32           deopts;
        u32          *osr;
        u32           nosr;
        i32          *tier;
        bool          entry_thunk;
        bool          gc_owned;
};

typedef union lir_scalar {
        i64    i;
        u64    u;
        double f64;
        float  f32;
        void  *ptr;
} LirScalar;

typedef struct lir_entry_frame {
        Value       *out;
        Value const *args;
        void        *base;
        usize        capacity;
        usize        top;
} LirEntryFrame;

typedef struct lir_runtime {
        volatile sig_atomic_t *interrupt;
        i32 (*poll)(Ty *, Value *, void const *);
        Ty *(*current_ty)(void);
        void (*arity_error)(Ty *, i32, i32);
        void (*arg_type_error)(Ty *, i32, LirType, Value const *);
        void *(*ptr_from)(Ty *, LirEntryFrame *, i32);
        void *(*ref_from)(Ty *, Value const *, i32);
        void (*reserve)(Ty *, LirEntryFrame *, u32);
        Value *(*restore)(Ty *, LirEntryFrame *);
        void (*unlock)(Ty *);
        void (*lock)(Ty *);
        void (*interpret_error)(Ty *, LirError const *);
} LirRuntime;

struct lir_target {
        LirArch     arch;
        LirABI      abi;
        char const *name;
        LirRegPool  gpr;
        LirRegPool  fpr;
        u8          pins[LIR_MAX_PINS];
        u8          npins;
        u8          stack_align;
        bool (*legalize)(Lir *, LirConstraint **, u32 *, LirError *);
        bool (*emit)(Lir const *, LirAlloc const *, LirCode *, LirError *);
};

typedef struct jit_mapping {
        void *rw;
        void *rx;
} JitMapping;

typedef struct jitmem_stats {
        usize allocated;
        usize used;
        usize nchunks;
} JitMemStats;

typedef struct lir_bytes {
        u8   *items;
        usize count;
        struct lir_binding *holes;
        u32 nholes;
        u32 ninputs;
} LirBytes;

typedef struct lir_binding {
        LirOpnd operand;
        Value  *value;
        LirSig const *signature;
        u32 flags;
} LirBinding;

LirClass lir_type_class(LirType type);
u32 lir_type_size(LirType type);
Lir *lir_new(char const *name, LirSig const *sig, LirMode mode, LirError *err);
void lir_free(Lir *L);
void lir_destroy(Lir *L);
Lir *lir_adopt(Ty *ty, Lir *L);
void lir_mark(Ty *ty, Lir *L);
LirReg lir_reg(Lir *L, LirClass cls);
LirReg lir_pinned(Lir *L, LirPin pin);
bool lir_pin_param(Lir *L, LirPin pin, u32 param);
bool lir_pc_param(Lir *L, u32 param);
LirLabel lir_label(Lir *L);
bool lir_bind(Lir *L, LirLabel label);
bool lir_entry(Lir *L, LirLabel label);
LirReg lir_vslot(Lir *L);
LirOpnd lir_const(Lir *L, Value const *value);
LirOpnd lir_ref_const(Lir *L, Value const *value);
bool lir_emit(Lir *L, LirInst const *inst);
bool lir_emit_owned(Lir *L, LirInst const *inst);
bool lir_emit_to(Lir *L, LirOp op, LirReg dst, LirOpnd const *args, u32 nargs);
bool lir_cfg(Lir const *L, LirCFG *cfg, LirError *err);
void lir_cfg_free(LirCFG *cfg);
bool lir_validate(Lir *L, LirError *err);
void lir_cfg_free(LirCFG *cfg);
bool lir_prepare(Lir *L, LirError *err);
bool lir_serialize(Lir *L, LirBytes *bytes, LirError *err);
Lir *lir_deserialize(void const *bytes, usize size, LirBinding const *holes,
                     u32 nholes, LirError *err);
void lir_bytes_free(LirBytes *bytes);
void lir_dump(Lir const *L, FILE *out);
Lir *lir_build_entry(LirCode *code, LirError *err);
bool lir_legalize(Lir *L, LirTarget const *target, LirConstraint **constraints,
                  u32 *nconstraints, LirError *err);
bool lir_allocate(Lir const *L, LirCFG const *cfg, LirTarget const *target,
                  LirConstraint const *constraints, u32 nconstraints,
                  LirAlloc *alloc, LirError *err);
bool lir_allocate_workspaces(Lir const *L, LirTarget const *target,
                             LirAlloc *alloc, LirError *err);
u8 lir_physical(LirAlloc const *alloc, LirReg reg, u32 op, bool output);
void lir_alloc_free(LirAlloc *alloc);
bool lir_parallel_moves(LirMove const *moves, u32 count, LirRegPool const *pool,
                       LirMove **out, u32 *nout, LirError *err);
LirTarget const *lir_target(void);
Lir *lir_clone(Lir *L, LirError *err);
bool lir_normalize(Lir *L, LirError *err);
LirCode *lir_finish(Lir *L, bool entry, LirError *err);
LirCode *lir_finish_interpreted(Lir *L, bool entry, LirError *err);
LirCode *lir_finish_owned(Lir *L, LirError *err);
bool lir_interp_emit(LirCode *code, LirError *err);
void lir_interp_destroy(LirCode *code);
bool lir_interpret(Ty *ty, Lir const *L, LirScalar const *args, u32 nargs,
                   LirScalar *out, LirError *err);
bool lir_interpret_entry(Ty *ty, Lir const *L, LirLabel entry,
                         LirScalar const *args, u32 nargs,
                         LirScalar *out, LirError *err);
void lir_set_runtime(LirRuntime const *runtime);
LirRuntime const *lir_runtime(void);
void lir_code_mark(Ty *ty, LirCode *code);
LirCode *lir_code_adopt(Ty *ty, LirCode *code);
void lir_code_destroy(LirCode *code);
void lir_code_free(LirCode *code);
JitMapping jm_alloc(usize size);
void jm_write_begin(void);
bool jm_write_end(void *rx, usize size);
void jm_free(void *rx);
void jm_trim(void);
void jm_perf(void *rx, usize size, char const *name);
JitMemStats jm_stats(void);

inline static LirOpnd
lir_r(LirReg reg)
{
        return (LirOpnd) { .kind = LIR_OPERAND_REG, .reg = reg };
}

inline static LirOpnd
lir_i(i64 imm)
{
        return (LirOpnd) { .kind = LIR_OPERAND_IMM, .imm = imm };
}

inline static LirOpnd
lir_f(double imm)
{
        return (LirOpnd) { .kind = LIR_OPERAND_FIMM, .fimm = imm };
}

inline static LirOpnd
lir_m(LirReg base, LirReg index, u8 scale, i32 disp)
{
        return (LirOpnd) {
                .kind = LIR_OPERAND_MEM,
                .mem = { .base = base, .index = index, .scale = scale, .disp = disp }
        };
}

inline static LirOpnd
lir_l(LirLabel label)
{
        return (LirOpnd) { .kind = LIR_OPERAND_LABEL, .label = label };
}

inline static LirOpnd
lir_cc(LirCC cc)
{
        return (LirOpnd) { .kind = LIR_OPERAND_CC, .cc = cc };
}

inline static LirOpnd
lir_hole(LirOperandKind kind, u32 index)
{
        return (LirOpnd) { .kind = kind, .index = index };
}

#endif
