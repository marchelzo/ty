#ifndef COMPILE_H_INCLUDED
#define COMPILE_H_INCLUDED

#include "ty.h"
#include "value.h"

extern bool SuggestCompletions;
extern bool FindDefinition;
extern int QueryLine;
extern int QueryCol;
extern char const *QueryFile;
extern Symbol const *QueryResult;
extern Expr const *QueryExpr;

typedef struct location Location;
typedef struct expression Expr;
typedef struct symbol Symbol;

enum {
        TY_NAME_NONE,
        TY_NAME_VARIABLE,
        TY_NAME_NAMESPACE,
        TY_NAME_MODULE
};

enum {
        MOD_RELOADING = 1
};

enum {
        TYC_EVAL  = (1 << 0),
        TYC_PARSE = (1 << 1)
};

typedef struct eloc {
        union {
                uptr p_start;
                usize start_off;
        };

        union {
                uptr p_end;
                usize end_off;
        };

        Expr const *e;
} ExprLocation;

typedef struct expr_list ExprList;

struct expr_list {
        ExprList *next;
        Expr *e;
};

struct import {
        bool pub;
        char const *name;
        Module *mod;
};

typedef vec(struct import) import_vector;

typedef struct module {
        char *code;
        Scope *scope;
        import_vector imports;
        char const *name;
        char const *path;
        char const *source;
        Stmt **prog;
        TokenVector tokens;
        u64 flags;
} Module;

typedef vec(struct eloc) location_vector;

typedef struct {
        intrusive_vec(usize);
        int label;
} JumpGroup, offset_vector;

typedef struct {
        usize off;
        int label;
} JumpPlaceholder, JumpLabel;

typedef vec(JumpPlaceholder) JumpSet;

typedef struct loop_state {
        offset_vector continues;
        offset_vector breaks;
        i32 resources;
        i32 t;
        i32 n;
        bool wr;
} LoopState;

typedef struct {
        bool inclusive;
        bool reverse;

        Expr *start;
        Expr *stop;

        Expr *_if;
        Expr *_while;

        JumpLabel begin;
        JumpLabel next;

        JumpPlaceholder skip;
        JumpPlaceholder exit;
        JumpPlaceholder end;
} RangeLoop;

typedef struct try_state {
        u32 t;
        u8 ctx;
        bool need_trace;
} TryState;

typedef vec(LoopState) LoopStates;
typedef vec(TryState) TryStates;

typedef struct {
        int i;
        bool patched;
        byte_vector text;
        vec(char const *) captions;
        vec(char const *) map;
        uptr start;
        uptr end;
        char const *name;
        char const *module;
} ProgramAnnotation;

/*
 * State which is local to a single compilation unit.
 */
typedef struct compiler_state {
        byte_vector code;

        ProgramAnnotation annotation;

        JumpGroup match_fails;
        JumpGroup match_successes;
        expression_vector match_assignments;

        offset_vector generator_returns;

        symbol_vector bound_symbols;

        int function_resources;
        int resources;
        int label;

        int ctx;

        Scope *fscope;
        Scope *implicit_fscope;
        Scope *macro_scope;

        Expr *implicit_func;
        Expr *origin;

        statement_vector class_ops;
        statement_vector pending;

        bool _based;
        bool _eval;
        bool _parse;

        Type *expected_type;

        Expr *func;
        Expr *meth;
        Class *class;
        Symbol *self;

        int function_depth;

        TryStates tries;
        LoopStates loops;

        import_vector imports;

        StringVector ns;

        Scope *global;
        Scope *active;
        Scope *pscope;
        ScopeVector scopes;

        Module *module;

        Location start;
        Location end;

        Location mstart;
        Location mend;

        location_vector expression_locations;
        TokenVector source_tokens;
} CompileState;

void
compiler_init(Ty *ty);

int
compiler_get_completions(Ty *ty, char const *mod, char const *prefix, char **out, int max);

int
compiler_get_namespace_completions(
        Ty *ty,
        Expr const *ns,
        char const *prefix,
        char **out,
        int max
);

void
compiler_load_builtin_modules(Ty *ty);

Symbol *
compiler_introduce_symbol(Ty *ty, char const *, char const *);

int
compiler_introduce_tag(Ty *ty, char const *module, char const *name, int super);

bool
compiler_symbolize_expression(Ty *ty, Expr *e, Scope *scope);

void
CompilerDoUse(Ty *ty, Stmt *s, Scope *scope);

void
compiler_clear_location(Ty *ty);

Module *
compiler_compile_source(
        Ty *ty,
        char const *source,
        char const *filename
);

int
compiler_symbol_count(Ty *ty);

struct symbol *
compiler_lookup(Ty *ty, char const *module, char const *name);

int
gettag(Ty *ty, char const *module, char const *name);

char *
compiler_load_prelude(Ty *ty);

Location
compiler_find_definition(Ty *ty, char const *file, int line, int col);

ExprLocation *
compiler_find_expr_x(Ty *ty, char const *code, bool func);

Expr const *
compiler_find_expr(Ty *ty, char const *ip);

Expr const *
compiler_find_func(Ty *ty, char const *ip);

char *
compiler_find_next_line(Ty *ty, char const *ip);

bool
compiler_has_module(Ty *ty, char const *path);

usize
compiler_global_count(Ty *ty);

Symbol *
compiler_global_sym(Ty *ty, usize i);

Value
compiler_render_template(Ty *ty, Expr *);

bool
compiler_import_module(Ty *ty, Stmt const *);

void
IntroduceDefinitions(Ty *ty, Stmt *stmt);

void
define_macro(Ty *ty, Stmt *, bool fun);

void
define_type(Ty *ty, Stmt *, Scope *);

void
define_class(Ty *ty, Stmt *);

void
define_tag(Ty *ty, Stmt *s);

void
define_function(Ty *ty, Stmt *);

void
define_operator(Ty *ty, Scope *scope, Stmt *s);

bool
is_macro(Ty *ty, char const *module, char const *id);

bool
is_fun_macro(Ty *ty, char const *module, char const *id);

Value
tyexpr(Ty *ty, Expr const *);

Value
tyeval(Ty *ty, Expr *e);

Value
tystmt(Ty *ty, Stmt *s);

Expr *
cexpr(Ty *ty, Value *);

Expr *
TyToCExpr(Ty *ty, Value *v);

Value
CToTyExpr(Ty *ty, Expr *);

Value
CToTyStmt(Ty *ty, Stmt *);

Expr *
typarse(Ty *ty, Expr *e, Expr *self, Location const *start, Location const *end);

Value
compiler_eval(Ty *ty, Expr *e);

Stmt *
cstmt(Ty *ty, Value *);

void
compiler_set_type_of(Ty *ty, Stmt *);

void
colorize_code(
        char const *expr_color,
        char const *base_color,
        Location const *start,
        Location const *end,
        char *out,
        usize n
);

char const *
show_expr_type(Ty *ty, Expr const *e);

char *
show_expr(Expr const *e);

u32
source_register(Ty *ty, void const *src);

void *
source_lookup(Ty *ty, u32 src);

void
ForgetSourceNodesFrom(void const *base);

void
try_symbolize_application(Ty *ty, Scope *scope, Expr *e);

int
WriteExpressionTrace(Ty *ty, byte_vector *out, Expr const *e, int etw, bool first);

int
WriteExpressionOrigin(Ty *ty, byte_vector *out, Expr const *e);

void
WriteExpressionSourceHeading(Ty *ty, byte_vector *out, int cols, Expr const *e);

void
WriteExpressionSourceContext(Ty *ty, byte_vector *out, Expr const *e);

int
CompilationDepth(Ty *ty);

Value
CompilationTraceArray(Ty *ty);

void
CompilationTrace(Ty *ty, byte_vector *out);

CompileState
PushCompilerState(Ty *ty, char const *name, u32 flags);

void
PopCompilerState(Ty *ty, CompileState state);

CompileState *
TyCompilerState(Ty *ty);

void
CompilerScopePush(Ty *ty);

void
CompilerScopePop(Ty *ty);

bool
IsTopLevel(Symbol const *sym);

Scope *
GetNamespace(Ty *ty, Namespace *ns);

void
CompilerBlackpill(Ty *ty, Stmt *s);

bool
CompilerResolveExpr(Ty *ty, Expr *e);

void *
CompilerPushContext(Ty *ty, void const *ctx);

char const *
GetExpressionModule(Expr const *e);

bool
CompilerGetModuleTokens(Ty *ty, TokenVector *out, char const *mod);

char const *
CompilerGetModuleSource(Ty *ty, char const *mod);

Module *
CompilerGetModule(Ty *ty, char const *name);

Module *
CompilerCurrentModule(Ty *ty);

bool
CompilerReloadModule(Ty *ty, Module *mod, char const *source);

Symbol *
CompilerFindDefinition(Ty *ty, Module *mod, i32 line, i32 col);

bool
CompilerSuggestCompletions(
        Ty *ty,
        Module *mod,
        i32 line,
        i32 col,
        ValueVector *completions
);

void
CompilerResetState(Ty *ty);

int
Expr2Op(Expr const *e);

char const *
DumpProgram(
        Ty *ty,
        byte_vector *out,
        char const *name,
        char const *code,
        char const *end,
        bool incl_sub_fns
);

inline static bool
ModuleIsReloading(Module const *mod)
{
        return (mod->flags & MOD_RELOADING);
}

void *
GetCompilerContext(Ty *ty);

void
SetCompilerContext(Ty *ty, void *ctx);

Value
TyTraceEntryFor(Ty *ty, Expr const *e);

#endif

/* vim: set sw=8 sts=8 expandtab: */
