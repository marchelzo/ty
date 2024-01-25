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

char const *
compiler_get_location(char const *code, struct location *start, struct location *end);

bool
compiler_has_module(char const *path);

struct value
compiler_render_template(struct expression *);

void
import_module(struct statement const *);

void
define_macro(struct statement *);

void
define_class(struct statement *);

void
define_function(struct statement *);

bool
is_macro(struct expression const *e);

struct value
tyexpr(struct expression const *);

struct value
tyeval(struct expression *e);

struct value
tystmt(struct statement *s);

struct expression *
cexpr(struct value *);

struct expression *
typarse(struct expression *, struct location const *start, struct location const *end);

struct statement *
cstmt(struct value *);

#endif
