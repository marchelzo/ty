#ifndef COMPILE_H_INCLUDED
#define COMPILE_H_INCLUDED

#include "value.h"

extern bool CheckConstraints;
struct location;
struct expression;
typedef struct symbol Symbol;

struct eloc {
        union {
                uintptr_t p_start;
                size_t start_off;
        };
        union {
                uintptr_t p_end;
                size_t end_off;
        };
        Location start;
        Location end;
        char const *filename;
        Expr const *e;
};

typedef struct expr_list ExprList;

struct expr_list {
        ExprList *next;
        Expr *e;
};

struct import {
        bool pub;
        char const *name;
        Scope *scope;
};

typedef vec(struct import) import_vector;

struct module {
        char const *path;
        char *code;
        Scope *scope;
        import_vector imports;
};

typedef vec(struct eloc)      location_vector;
typedef vec(Symbol *)         symbol_vector;

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
typedef struct state {
        byte_vector code;

        ProgramAnnotation annotation;

        offset_vector selfs;

        JumpGroup match_fails;
        JumpGroup match_successes;

        offset_vector generator_returns;

        symbol_vector bound_symbols;

        int function_resources;
        int resources;

        int label;

        Scope *method;
        Scope *fscope;

        Scope *macro_scope;

        Scope *implicit_fscope;
        Expr *implicit_func;

        Expr *origin;

        statement_vector class_ops;

        Expr *func;
        int class;

        int function_depth;

        TryStates tries;
        LoopStates loops;

        import_vector imports;

        StringVector ns;

        Scope *global;

        char const *filename;
        Location start;
        Location end;

        Location mstart;
        Location mend;

        location_vector expression_locations;
} CompileState;

char const *
compiler_error(Ty *ty);

void
compiler_init(Ty *ty);

int
compiler_get_completions(Ty *ty, char const *mod, char const *prefix, char **out, int max);

void
compiler_load_builtin_modules(Ty *ty);

void
compiler_introduce_symbol(Ty *ty, char const *, char const *);

void
compiler_introduce_tag(Ty *ty, char const *module, char const *name);

bool
compiler_symbolize_expression(Ty *ty, struct expression *e, struct scope *scope);

void
compiler_clear_location(Ty *ty);

char *
compiler_compile_source(Ty *ty, char const *source, char const *filename);

int
compiler_symbol_count(Ty *ty);

struct symbol *
compiler_lookup(Ty *ty, char const *module, char const *name);

int
gettag(Ty *ty, char const *module, char const *name);

char *
compiler_load_prelude(Ty *ty);

struct location
compiler_find_definition(Ty *ty, char const *file, int line, int col);

Expr const *
compiler_find_expr(Ty *ty, char const *ip);

bool
compiler_has_module(Ty *ty, char const *path);

int
compiler_global_count(Ty *ty);

Symbol *
compiler_global_sym(Ty *ty, int i);

struct value
compiler_render_template(Ty *ty, struct expression *);

bool
compiler_import_module(Ty *ty, struct statement const *);

void
define_macro(Ty *ty, struct statement *, bool fun);

void
define_class(Ty *ty, struct statement *);

void
define_tag(Ty *ty, struct statement *s);

void
define_function(Ty *ty, struct statement *);

bool
is_macro(Ty *ty, char const *module, char const *id);

bool
is_fun_macro(Ty *ty, char const *module, char const *id);

struct value
tyexpr(Ty *ty, struct expression const *);

struct value
tyeval(Ty *ty, struct expression *e);

struct value
tystmt(Ty *ty, struct statement *s);

struct expression *
cexpr(Ty *ty, struct value *);

struct expression *
TyToCExpr(Ty *ty, struct value *v);

Value
CToTyExpr(Ty *ty, Expr *);

Value
CToTyStmt(Ty *ty, Stmt *);

struct expression *
typarse(Ty *ty, struct expression *, struct location const *start, struct location const *end);

struct statement *
cstmt(Ty *ty, struct value *);

void *
compiler_swap_jb(Ty *ty, void *);

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

uint32_t
source_register(Ty *ty, void const *src);

void *
source_lookup(Ty *ty, uint32_t src);

void
source_forget_arena(void const *arena);

void
try_symbolize_application(Ty *ty, struct scope *scope, struct expression *e);

int
WriteExpressionTrace(Ty *ty, char *out, int cap, Expr const *e, int etw, bool first);

int
WriteExpressionOrigin(Ty *ty, char *out, int cap, Expr const *e);

int
CompilationDepth(Ty *ty);

char *
CompilationTrace(Ty *ty);

CompileState
PushCompilerState(Ty *ty, char const *filename);

void
PopCompilerState(Ty *ty, CompileState state);

bool
IsTopLevel(Symbol const *sym);

char const *
DumpProgram(Ty *ty, byte_vector *out, char const *name, char const *code, char const *end);

#endif
