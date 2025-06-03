#ifndef COMPILE_H_INCLUDED
#define COMPILE_H_INCLUDED

#include "ty.h"
#include "value.h"

extern bool CheckConstraints;

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

typedef struct eloc {
        union {
                uintptr_t p_start;
                size_t start_off;
        };

        union {
                uintptr_t p_end;
                size_t end_off;
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
        intrusive_vec(size_t);
        int label;
} JumpGroup;

typedef JumpGroup offset_vector;

typedef struct {
        size_t off;
        int label;
} JumpPlaceholder, JumpLabel;

typedef struct loop_state {
        offset_vector continues;
        offset_vector breaks;
        int resources;
        int t;
        bool wr;
        bool each;
} LoopState;

typedef struct try_state {
        int t;
        bool finally;
} TryState;

typedef vec(LoopState) LoopStates;
typedef vec(TryState) TryStates;

typedef struct {
        int i;
        bool patched;
        byte_vector text;
        vec(char const *) captions;
        vec(char const *) map;
        uintptr_t start;
        uintptr_t end;
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

        bool based;

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

int
compiler_global_count(Ty *ty);

Symbol *
compiler_global_sym(Ty *ty, int i);

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
        size_t n
);

char const *
show_expr_type(Ty *ty, Expr const *e);

char *
show_expr(Expr const *e);

uint32_t
source_register(Ty *ty, void const *src);

void *
source_lookup(Ty *ty, uint32_t src);

void
source_forget_arena(void const *arena);

void
try_symbolize_application(Ty *ty, Scope *scope, Expr *e);

int
WriteExpressionTrace(Ty *ty, byte_vector *out, Expr const *e, int etw, bool first);

int
WriteExpressionOrigin(Ty *ty, byte_vector *out, Expr const *e);

int
CompilationDepth(Ty *ty);

Value
CompilationTraceArray(Ty *ty);

void
CompilationTrace(Ty *ty, byte_vector *out);

CompileState
PushCompilerState(Ty *ty, char const *filename);

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

#endif

/* vim: set sw=8 sts=8 expandtab: */
