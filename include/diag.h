#ifndef DIAG_H_INCLUDED
#define DIAG_H_INCLUDED

#include "ty.h"

typedef struct diag_sink {
        ValueVector errors;
        ExprVec     nodes;
        ValueVector suppressed;
        u32 flags;
} DiagSink;

enum {
        DIAG_RECOVER = 1 << 0
};

extern bool TraceThrows;

void
TyDiagInit(void);

Value
TyNewCompileError(
        Ty *ty,
        char const *kind,
        char const *msg,
        Value locs,
        char const *text,
        Value cause,
        Value detail
);

Value
TyWrapError(
        Ty *ty,
        Value cause,
        Value detail,
        Expr const *where,
        char const *fmt,
        ...
);

bool
TyIsCompileError(Value const *v);

bool
TyErrorIsKind(Ty *ty, Value const *v, char const *kind);

bool
TyErrorIsFrom(Ty *ty, Value const *v, Module const *mod);

void
TyFormatError(Ty *ty, Value const *exc, Value const *detail, byte_vector *out);

void
TyErrorBrief(Ty *ty, Value const *exc, byte_vector *out);

Value
TyErrorRecords(Ty *ty, Value const *exc);

void
TySetError(Ty *ty, Value exc, Value detail);

Value
TyErrorMessage(Ty *ty, char const *text);

Value
TyCatchFail(Ty *ty);

Value
TyCatchDetail(Ty *ty, Value *detail);

Value
TyCatchWrap(Ty *ty, Expr const *where, char const *fmt, ...);

void
TySuppress(Ty *ty, Value exc, char const *what);

void
TyDiagPush(Ty *ty, u32 flags);

void
TyDiagRecord(Ty *ty, Value err, Expr const *node);

Value
TyDiagFail(Ty *ty, Value exc, bool *replaced);

Value
TyDiagFinish(Ty *ty);

bool
TyDiagRecovering(Ty *ty);

Value
TyDiagFindPoison(Ty *ty, Expr const *e);

void
TyDiagMark(Ty *ty);

#endif

/* vim: set sts=8 sw=8 expandtab: */
