#ifndef PANIC_H_INCLUDED
#define PANIC_H_INCLUDED

#include <stdnoreturn.h>

noreturn void
panic(char const *fmt, ...);

#endif
