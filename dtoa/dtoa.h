#ifndef TY_DTOA_H_INCLUDED
#define TY_DTOA_H_INCLUDED

#include "SwiftDtoa.h"


inline static size_t
dtoa(double x, void *buf, size_t n)
{
        return swift_dtoa_optimal_double(x, buf, n);
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
