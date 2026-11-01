#ifndef CHRONO_H_INCLUDED
#define CHRONO_H_INCLUDED

#include <time.h>

#include "ty.h"

enum : i64 {
        TY_NS = 1,
        TY_US = 1000 * TY_NS,
        TY_MS = 1000 * TY_US,
        TY_S  = 1000 * TY_MS,
        TY_M  =   60 * TY_S,
        TY_H  =   60 * TY_M,
        TY_D  =   24 * TY_H
};

typedef enum {
        CHRONO_OK,
        CHRONO_OVERFLOW,
        CHRONO_ZERO,
        CHRONO_BAD
} ChronoStatus;

#define IsDelta(v) ((v)->type == VALUE_DURATION || (v)->type == VALUE_TIMEDELTA)

noreturn void
ChronoOverflow(Ty *ty);

i64
ChronoNow(Ty *ty, i64 clk);

char const *
ChronoClockName(i64 clk);

isize
ChronoUnit(char const *s, char const *end, i64 *unit);

void
ChronoShowDuration(Ty *ty, byte_vector *buf, i64 ns);

void
ChronoShowTime(Ty *ty, byte_vector *buf, i64 ns, i64 clk);

ChronoStatus
ChronoLiteral(bool real, double x, i64 k, i64 unit, i64 *ns);

ChronoStatus
ChronoParse(char const *s, usize n, bool sign, i64 *ns);

ChronoStatus
ChronoTryScale(i64 ns, Value const *k, i64 *out);

ChronoStatus
ChronoTryDivide(i64 ns, Value const *k, i64 *out);

i64
ChronoScale(Ty *ty, i64 ns, Value const *k);

i64
ChronoDivide(Ty *ty, i64 ns, Value const *k);

i64
ChronoSpan(Ty *ty, Value const *a, Value const *b);

i64
ChronoTimeout(Ty *ty, char const *ctx, Value const *v);

i64
ChronoDeadline(Ty *ty, char const *ctx, Value const *v, i64 clk);

i64
ChronoInstant(Ty *ty, char const *ctx, Value const *v, i64 clk);

i64
ChronoDuration(Ty *ty, char const *ctx, Value const *v);

Value
ChronoConstruct(Ty *ty, int class_id, int argc);

struct timespec
ChronoTimespec(i64 ns);

inline static i64
ChronoAdd(Ty *ty, i64 a, i64 b)
{
        i64 c;

        if (__builtin_add_overflow(a, b, &c)) {
                ChronoOverflow(ty);
        }

        return c;
}

inline static i64
ChronoSub(Ty *ty, i64 a, i64 b)
{
        i64 c;

        if (__builtin_sub_overflow(a, b, &c)) {
                ChronoOverflow(ty);
        }

        return c;
}

inline static i64
ChronoSeconds(Ty *ty, i64 sec)
{
        i64 ns;

        if (__builtin_mul_overflow(sec, TY_S, &ns)) {
                ChronoOverflow(ty);
        }

        return ns;
}

inline static i64
ChronoMsCeil(i64 ns)
{
        return (ns < 0) ? -1 : (ns / TY_MS) + (ns % TY_MS != 0);
}

#define TIMEOUT_NS_ARG(i)    ChronoTimeout(ty, _name__, &ARG(i))
#define TIMEOUT_MS_ARG(i)    ChronoMsCeil(TIMEOUT_NS_ARG(i))
#define DURATION_NS_ARG(i)   ChronoDuration(ty, _name__, &ARG(i))
#define INSTANT_ARG(i, clk)  ChronoInstant(ty, _name__, &ARG(i), (clk))

#endif
