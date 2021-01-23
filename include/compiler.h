#ifndef COMPILE_H_INCLUDED
#define COMPILE_H_INCLUDED

char const *
compiler_error(void);

void
compiler_init(void);

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

#endif
