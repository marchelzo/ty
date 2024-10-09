#ifndef COMPILE_H_INCLUDED
#define COMPILE_H_INCLUDED

#include "value.h"

extern bool CheckConstraints;
struct location;
struct expression;
typedef struct symbol Symbol;

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

bool
IsTopLevel(Symbol const *sym);

char const *
DumpProgram(Ty *ty, byte_vector *out, char const *name, char const *code, char const *end);

#endif
