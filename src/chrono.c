#include <ctype.h>
#include <errno.h>
#include <math.h>
#include <string.h>
#include <time.h>

#include "ty.h"
#include "chrono.h"
#include "lex.h"
#include "value.h"
#include "vm.h"
#include "xd.h"

static struct {
        i64         u;
        char const *s;
        int         digits;
} const Units[] = {
        { TY_D,  "d",  3 },
        { TY_H,  "h",  3 },
        { TY_M,  "m",  3 },
        { TY_S,  "s",  9 },
        { TY_MS, "ms", 6 },
        { TY_US, "us", 3 },
        { TY_NS, "ns", 0 }
};

noreturn void
ChronoOverflow(Ty *ty)
{
        zP("time arithmetic overflowed the 64-bit nanosecond range");
}

i64
ChronoNow(Ty *ty, i64 clk)
{
        struct timespec t;

        if (clock_gettime((clockid_t)clk, &t) != 0) {
                zP("clock_gettime(%s): %s", ChronoClockName(clk), strerror(errno));
        }

        return TY_S * t.tv_sec + t.tv_nsec;
}

char const *
ChronoClockName(i64 clk)
{
#define X(c) case c: return #c;
        switch (clk) {
        X(CLOCK_REALTIME)
#ifndef _WIN32
        X(CLOCK_MONOTONIC)
#endif
#ifdef CLOCK_REALTIME_COARSE
        X(CLOCK_REALTIME_COARSE)
#endif
#ifdef CLOCK_MONOTONIC_COARSE
        X(CLOCK_MONOTONIC_COARSE)
#endif
#ifdef CLOCK_MONOTONIC_RAW
        X(CLOCK_MONOTONIC_RAW)
#endif
#ifdef CLOCK_BOOTTIME
        X(CLOCK_BOOTTIME)
#endif
#ifdef CLOCK_TAI
        X(CLOCK_TAI)
#endif
#ifdef CLOCK_PROCESS_CPUTIME_ID
        X(CLOCK_PROCESS_CPUTIME_ID)
#endif
#ifdef CLOCK_THREAD_CPUTIME_ID
        X(CLOCK_THREAD_CPUTIME_ID)
#endif
        }
#undef X

        return NULL;
}

static bool
IsCalendarClock(i64 clk)
{
        switch (clk) {
        case CLOCK_REALTIME:
#ifdef CLOCK_REALTIME_COARSE
        case CLOCK_REALTIME_COARSE:
#endif
#ifdef CLOCK_TAI
        case CLOCK_TAI:
#endif
                return true;
        }

        return false;
}

isize
ChronoUnit(char const *s, char const *end, i64 *unit)
{
        for (int i = 0; i < countof(Units); ++i) {
                usize n = strlen(Units[i].s);
                if (
                        (s + n <= end)
                     && (memcmp(s, Units[i].s, n) == 0)
                     && (
                                (s + n == end)
                             || !(isalnum((u8)s[n]) || s[n] == '_')
                        )
                ) {
                        *unit = Units[i].u;
                        return n;
                }
        }

        return 0;
}

static void
ShowFraction(Ty *ty, byte_vector *buf, u64 frac, u64 u, int digits)
{
        char out[16];
        u64 scale = 1;

        for (int i = 0; i < digits; ++i) {
                scale *= 10;
        }

        frac = frac * scale / u;

        while (digits > 0 && frac % 10 == 0) {
                frac   /= 10;
                digits -= 1;
        }

        if (digits > 0) {
                snprintf(out, sizeof out, ".%0*"PRIu64, digits, frac);
                svPn(*buf, out, strlen(out));
        }
}

void
ChronoShowDuration(Ty *ty, byte_vector *buf, i64 ns)
{
        char out[32];
        u64 n = (ns < 0) ? -(u64)ns : (u64)ns;

        if (n == 0) {
                svPn(*buf, "0s", 2);
                return;
        }

        if (ns < 0) {
                svP(*buf, '-');
        }

        for (int i = 0; i < countof(Units); ++i) {
                u64 u = Units[i].u;
                if (
                        (n >= u)
                     && (u < TY_M || n % (u / 1000) == 0)
                ) {
                        snprintf(out, sizeof out, "%"PRIu64, n / u);
                        svPn(*buf, out, strlen(out));
                        ShowFraction(ty, buf, n % u, u, Units[i].digits);
                        svPn(*buf, Units[i].s, strlen(Units[i].s));
                        return;
                }
        }
}

void
ChronoShowTime(Ty *ty, byte_vector *buf, i64 ns, i64 clk)
{
        char const *name = ChronoClockName(clk);
        struct tm   tm   = {0};
        time_t      sec;
        char        out[64];

        if (name != NULL) {
                sxdf(buf, "Time(%s, ", name);
        } else {
                sxdf(buf, "Time(%"PRIi64", ", clk);
        }

        if (!IsCalendarClock(clk)) {
                ChronoShowDuration(ty, buf, ns);
                svP(*buf, ')');
                return;
        }

        sec = (time_t)(ns / TY_S) - (ns % TY_S < 0);

        gmtime_r(&sec, &tm);
        strftime(out, sizeof out, "%Y-%m-%dT%H:%M:%S", &tm);
        svPn(*buf, out, strlen(out));
        ShowFraction(ty, buf, (u64)(ns - (i64)sec * TY_S), TY_S, 9);
        svPn(*buf, "Z)", 2);
}

static char const *
UnitName(i64 u)
{
        for (int i = 0; i < countof(Units); ++i) {
                if (Units[i].u == u) {
                        return Units[i].s;
                }
        }

        return "ns";
}

static i64
UnitFor(u64 n)
{
        for (int i = 0; i < countof(Units); ++i) {
                if (n >= (u64)Units[i].u) {
                        return Units[i].u;
                }
        }

        return TY_S;
}

static void
ShowScaled(Ty *ty, byte_vector *buf, i64 ns, i64 u, int prec, bool point)
{
        typedef unsigned __int128 u128;
        char out[48];
        u64  n = (ns < 0) ? -(u64)ns : (u64)ns;
        int  p = (prec < 0) ? 9 : min(prec, 18);
        u64  k = 1;
        u128 q;
        u64  whole;
        u64  frac;

        for (int i = 0; i < p; ++i) {
                k *= 10;
        }

        q     = ((u128)n * k * 2 + (u64)u) / ((u128)u * 2);
        whole = (u64)(q / k);
        frac  = (u64)(q % k);

        while (prec < 0 && p > 0 && frac % 10 == 0) {
                frac /= 10;
                p    -= 1;
        }

        if (ns < 0 && q != 0) {
                svP(*buf, '-');
        }

        snprintf(out, sizeof out, "%"PRIu64, whole);
        svPn(*buf, out, strlen(out));

        if (p > 0) {
                snprintf(out, sizeof out, ".%0*"PRIu64, p, frac);
                svPn(*buf, out, strlen(out));
        } else if (point && prec < 0) {
                svPn(*buf, ".0", 2);
        }

        for (int i = 18; i < prec; ++i) {
                svP(*buf, '0');
        }
}

void
ChronoStrftime(Ty *ty, byte_vector *buf, char const *s, usize n, i64 ns, i64 clk)
{
        byte_vector f   = {0};
        struct tm   tm  = {0};
        time_t      sec = (time_t)(ns / TY_S) - (ns % TY_S < 0);
        i64         sub = ns - (i64)sec * TY_S;
        char        digits[16];
        char       *out = TY_TMP();
        usize       r;

        if (IsCalendarClock(clk)) {
                localtime_r(&sec, &tm);
        } else {
                gmtime_r(&sec, &tm);
        }

        snprintf(digits, sizeof digits, "%09"PRIi64, sub);

        for (usize i = 0; i < n; ++i) {
                usize j = i + 1;
                int   w = 0;

                if (s[i] != '%') {
                        svP(f, s[i]);
                        continue;
                }

                while (j < n && isdigit((u8)s[j])) {
                        w  = 10 * min(w, 99) + (s[j] - '0');
                        j += 1;
                }

                if (j < n && s[j] == 'N') {
                        svPn(f, digits, (w == 0 || w > 9) ? 9 : w);
                        i = j;
                } else if (j < n) {
                        svPn(f, s + i, j - i + 1);
                        i = j;
                } else {
                        svPn(f, s + i, j - i);
                        i = j - 1;
                }
        }

        svP(f, '\0');

        r = strftime(out, TY_TMP_N, vv(f), &tm);

        svPn(*buf, out, r);
}

void
ChronoShowText(Ty *ty, byte_vector *buf, i64 ns, i64 clk)
{
        static char const DateFormat[] = "%a %b %e %I:%M:%S %p %Z %Y";

        if (IsCalendarClock(clk)) {
                ChronoStrftime(ty, buf, DateFormat, sizeof DateFormat - 1, ns, clk);
        } else {
                ShowScaled(ty, buf, ns, TY_S, -1, true);
        }
}

static int
FormatPrecision(char const **s, char const *end)
{
        int p = 0;

        if (*s == end || **s != '.') {
                return -1;
        }

        *s += 1;

        if (*s == end || !isdigit((u8)**s)) {
                return -2;
        }

        while (*s < end && isdigit((u8)**s)) {
                p   = 10 * min(p, 99) + (**s - '0');
                *s += 1;
        }

        return p;
}

bool
ChronoFormat(Ty *ty, byte_vector *buf, Value const *v, char const *s, usize n)
{
        char const *end  = s + n;
        u64         abs  = (v->ns < 0) ? -(u64)v->ns : (u64)v->ns;
        i64         unit = 0;
        int         prec;

        if (v->type == VALUE_TIME && memchr(s, '%', n) != NULL) {
                ChronoStrftime(ty, buf, s, n, v->ns, v->clk);
                return true;
        }

        prec = FormatPrecision(&s, end);

        if (prec == -2) {
                return false;
        }

        if (v->type == VALUE_TIME) {
                if (s != end) {
                        return false;
                }
                if (prec == -1) {
                        ChronoShowText(ty, buf, v->ns, v->clk);
                } else {
                        ShowScaled(ty, buf, v->ns, TY_S, prec, true);
                }
                return true;
        }

        if (s != end && ChronoUnit(s, end, &unit) != end - s) {
                return false;
        }

        if (unit == 0 && prec == -1) {
                ChronoShowDuration(ty, buf, v->ns);
                return true;
        }

        unit = (unit != 0) ? unit : UnitFor(abs);

        ShowScaled(ty, buf, v->ns, unit, prec, false);
        svPn(*buf, UnitName(unit), strlen(UnitName(unit)));

        return true;
}

static ChronoStatus
Fits(double x, i64 *out)
{
        if (!(x >= -0x1p63 && x < 0x1p63)) {
                return CHRONO_OVERFLOW;
        }

        *out = (i64)x;

        return CHRONO_OK;
}

ChronoStatus
ChronoLiteral(bool real, double x, i64 k, i64 unit, i64 *ns)
{
        if (real) {
                return (x >= 0.0) ? Fits(round(x * (double)unit), ns) : CHRONO_OVERFLOW;
        }

        return (k < 0 || __builtin_mul_overflow(k, unit, ns)) ? CHRONO_OVERFLOW : CHRONO_OK;
}

ChronoStatus
ChronoParse(char const *s, usize n, bool sign, i64 *ns)
{
        NumLit      lit;
        bool        neg = sign && (n > 0) && (s[0] == '-');
        char const *p   = s + neg;

        if (!isdigit((u8)*p)) {
                return CHRONO_BAD;
        }

        ScanNumber(p, s + n, true, &lit);

        if (lit.err == NUM_DURATION_RANGE) {
                return CHRONO_OVERFLOW;
        }

        if (
                (lit.err != NUM_OK)
             || !lit.duration
             || (p + lit.n != s + n)
        ) {
                return CHRONO_BAD;
        }

        *ns = neg ? -lit.ns : lit.ns;

        return CHRONO_OK;
}

ChronoStatus
ChronoTryScale(i64 ns, Value const *k, i64 *out)
{
        switch (k->type) {
        case VALUE_INTEGER:
                return __builtin_mul_overflow(ns, k->z, out) ? CHRONO_OVERFLOW : CHRONO_OK;

        case VALUE_REAL:
                return Fits(round((double)ns * k->real), out);

        default:
                return CHRONO_BAD;
        }
}

ChronoStatus
ChronoTryDivide(i64 ns, Value const *k, i64 *out)
{
        switch (k->type) {
        case VALUE_INTEGER:
                if (k->z == 0) {
                        return CHRONO_ZERO;
                }
                if (k->z == -1 && ns == INT64_MIN) {
                        return CHRONO_OVERFLOW;
                }
                *out = ns / k->z;
                return CHRONO_OK;

        case VALUE_REAL:
                return (k->real == 0.0) ? CHRONO_ZERO : Fits(round((double)ns / k->real), out);

        default:
                return CHRONO_BAD;
        }
}

static i64
Settle(Ty *ty, ChronoStatus st, i64 ns, char const *verb, Value const *k)
{
        switch (st) {
        case CHRONO_OK:       return ns;
        case CHRONO_OVERFLOW: ChronoOverflow(ty);
        case CHRONO_ZERO:     ZeroDividePanic(ty);
        default:              zP("cannot %s a time interval by %s", verb, VSC(k));
        }
}

i64
ChronoScale(Ty *ty, i64 ns, Value const *k)
{
        i64          r  = 0;
        ChronoStatus st = ChronoTryScale(ns, k, &r);

        return Settle(ty, st, r, "scale", k);
}

i64
ChronoDivide(Ty *ty, i64 ns, Value const *k)
{
        i64          r  = 0;
        ChronoStatus st = ChronoTryDivide(ns, k, &r);

        return Settle(ty, st, r, "divide", k);
}

i64
ChronoSpan(Ty *ty, Value const *a, Value const *b)
{
        if (a->clk != b->clk) {
                zP(
                        "cannot relate times from different clocks: %s and %s",
                        VSC(a),
                        VSC(b)
                );
        }

        return ChronoSub(ty, a->ns, b->ns);
}

i64
ChronoTimeout(Ty *ty, char const *ctx, Value const *v)
{
        i64 left;

        switch (v->type) {
        case VALUE_NONE:
        case VALUE_NIL:
                return -1;

        case VALUE_DURATION:
                return v->ns;

        case VALUE_TIME:
                left = ChronoSub(ty, v->ns, ChronoNow(ty, v->clk));
                return max(left, 0);

        default:
                zP("%s: expected a Duration or a Time but got %s", ctx, VSC(v));
        }
}

i64
ChronoDeadline(Ty *ty, char const *ctx, Value const *v, i64 clk)
{
        switch (v->type) {
        case VALUE_NONE:
        case VALUE_NIL:
                return -1;

        case VALUE_TIME:
                if (v->clk == clk) {
                        return v->ns;
                }
        case VALUE_DURATION:
                return ChronoAdd(ty, ChronoNow(ty, clk), ChronoTimeout(ty, ctx, v));

        default:
                zP("%s: expected a Duration or a Time but got %s", ctx, VSC(v));
        }
}

TyDeadline
ChronoWait(Ty *ty, char const *ctx, Value const *v)
{
        i64 ns;

        switch (v->type) {
        case VALUE_NONE:
        case VALUE_NIL:
                return TY_FOREVER;

        case VALUE_TIME:
                return (TyDeadline) { v->clk, TyInstantFromNs(v->ns) };

        case VALUE_DURATION:
                return __builtin_add_overflow(ChronoNow(ty, TY_WAIT_CLOCK), v->ns, &ns)
                     ? TY_FOREVER
                     : (TyDeadline) { TY_WAIT_CLOCK, TyInstantFromNs(ns) };

        default:
                zP("%s: expected a Duration or a Time but got %s", ctx, VSC(v));
        }
}

i64
ChronoInstant(Ty *ty, char const *ctx, Value const *v, i64 clk)
{
        if (v->type != VALUE_TIME) {
                zP("%s: expected a Time but got %s", ctx, VSC(v));
        }

        if (v->clk != clk) {
                zP(
                        "%s: expected a Time from %s but got %s",
                        ctx,
                        ChronoClockName(clk),
                        VSC(v)
                );
        }

        return v->ns;
}

i64
ChronoDuration(Ty *ty, char const *ctx, Value const *v)
{
        if (v->type != VALUE_DURATION) {
                zP("%s: expected a Duration but got %s", ctx, VSC(v));
        }

        return v->ns;
}

static noreturn void
BadText(Ty *ty, char const *ctx, char const *why, Value const *s)
{
        char  msg[256];
        Value exc;

        ty_snprintf(msg, sizeof msg, "%s: %s: '%.*s'", ctx, why, (int)min(sN(*s), 128), ss(*s));

        exc = NewInstance(CLASS_VALUE_ERROR, vSsz(msg));
        vmE(&exc);
}

static i64
ParseText(Ty *ty, char const *ctx, Value const *s, bool sign)
{
        i64 ns;

        switch (ChronoParse(TY_TMP_C_STR(*s), sN(*s), sign, &ns)) {
        case CHRONO_OK:       return ns;
        case CHRONO_OVERFLOW: BadText(ty, ctx, "out of range", s);
        default:              BadText(ty, ctx, "not a duration literal", s);
        }
}

static Value
NewDuration(Ty *ty, int argc)
{
        ASSERT_ARGC("Duration()", 1);

        Value x  = ARGx(0, VALUE_INTEGER, VALUE_STRING);
        i64   ns = (x.type == VALUE_STRING) ? ParseText(ty, _name__, &x, false) : x.z;

        if (ns < 0) {
                bP("a Duration can't be negative: %"PRIi64"ns", ns);
        }

        return DURATION(ns);
}

static Value
NewTimeDelta(Ty *ty, int argc)
{
        ASSERT_ARGC("TimeDelta()", 1);

        Value x = ARGx(0, VALUE_INTEGER, VALUE_STRING);

        return TIMEDELTA((x.type == VALUE_STRING) ? ParseText(ty, _name__, &x, true) : x.z);
}

static Value
NewTime(Ty *ty, int argc)
{
        ASSERT_ARGC("Time()", 2);
        return TIME(INT_ARG(0), INT_ARG(1));
}

Value
ChronoConstruct(Ty *ty, int class_id, int argc)
{
        switch (class_id) {
        case CLASS_DURATION:  return NewDuration(ty, argc);
        case CLASS_TIMEDELTA: return NewTimeDelta(ty, argc);
        default:              return NewTime(ty, argc);
        }
}

struct timespec
ChronoTimespec(i64 ns)
{
        i64 sec  = ns / TY_S;
        i64 nsec = ns % TY_S;

        if (nsec < 0) {
                sec  -= 1;
                nsec += TY_S;
        }

        return (struct timespec) { .tv_sec = sec, .tv_nsec = nsec };
}
