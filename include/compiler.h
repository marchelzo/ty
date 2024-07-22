#ifndef COMPILE_H_INCLUDED
#define COMPILE_H_INCLUDED

#include "value.h"

extern bool CheckConstraints;
struct location;
struct expression;

char const *
compiler_error(void);

void
compiler_init(void);

int
compiler_get_completions(char const *mod, char const *prefix, char **out, int max);

void
compiler_load_builtin_modules(void);

void
compiler_introduce_symbol(char const *, char const *);

void
compiler_introduce_tag(char const *module, char const *name);

bool
compiler_symbolize_expression(struct expression *e, struct scope *scope);

void
compiler_clear_location(void);

char *
compiler_compile_source(char const *source, char const *filename);

int
compiler_symbol_count(void);

struct symbol *
compiler_lookup(char const *module, char const *name);

int
gettag(char const *module, char const *name);

char *
compiler_load_prelude(void);

struct location
compiler_find_definition(char const *file, int line, int col);

Expr const *
compiler_find_expr(char const *ip);

bool
compiler_has_module(char const *path);

int
compiler_global_count(void);

struct value
compiler_render_template(struct expression *);

bool
compiler_import_module(struct statement const *);

void
define_macro(struct statement *, bool fun);

void
define_class(struct statement *);

void
define_function(struct statement *);

bool
is_macro(char const *module, char const *id);

bool
is_fun_macro(char const *module, char const *id);

struct value
tyexpr(struct expression const *);

struct value
tyeval(struct expression *e);

struct value
tystmt(struct statement *s);

struct expression *
cexpr(struct value *);

struct expression *
TyToCExpr(struct value *v);

struct expression *
typarse(struct expression *, struct location const *start, struct location const *end);

struct statement *
cstmt(struct value *);

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
show_expr_type(Expr const *e);

uint32_t
source_register(void const *src);

void *
source_lookup(uint32_t src);

void
source_forget_arena(void const *arena);

#endif
