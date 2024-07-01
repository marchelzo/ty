#ifndef POLYFILL_DLFCN_H_INCLUDED
#define POLYFILL_DLFCN_H_INCLUDED 1

#if defined(WIN32) || defined(_WIN32)
#include <windows.h>

#else
#include <dlfcn.h>
#endif

#endif
