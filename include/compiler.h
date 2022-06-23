#ifndef COMPILE_H_INCLUDED
#define COMPILE_H_INCLUDED

extern _Bool CheckConstraints;

char const *
compiler_error(void);

void
compiler_init(void);

int
compiler_get_completions(char const *mod, char const *prefix, char **out, int max);

void
compiler_introduce_symbol(char const *, char const *);

char *
compiler_compile_source(char const *source, char const *filename);

int
compiler_symbol_count(void);

char *
compiler_load_prelude(void);

char const *
compiler_get_location(char const *code, struct location *start, struct location *end);

bool
compiler_has_module(char const *path);

#endif
