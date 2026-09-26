#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#include "ty.h"
#include "value.h"
#include "ast.h"
#include "vm.h"
#include "compiler.h"
#include "diag.h"
#include "xd.h"

bool TraceThrows;

void
TyDiagInit(void)
{
        char const *s = getenv("TY_TRACE_THROWS");
        TraceThrows = (s != NULL) && (s[0] != '\0') && (s[0] != '0');
}

inline static Value
Member(Ty *ty, Value const *v, int id)
{
        Value *m = ObjectMember(*v, id);
        return (m == NULL) ? NIL : *m;
}

inline static Value
MemberStr(Ty *ty, Value const *v, int id)
{
        Value m = Member(ty, v, id);
        return (m.type == VALUE_STRING) ? m : xSz("");
}

bool
TyIsCompileError(Value const *v)
{
        return (v->type == VALUE_OBJECT)
            && (v->class == CLASS_COMPILE_ERROR);
}

bool
TyErrorIsFrom(Ty *ty, Value const *v, Module const *mod)
{
        if (!TyIsCompileError(v) || mod == NULL || mod->path == NULL) {
                return false;
        }

        Value locs = Member(ty, v, NAMES._locs);
        if (locs.type != VALUE_ARRAY || vN(*locs.array) == 0) {
                return false;
        }

        Value file = tget_or(v_(*locs.array, 0), "file", NIL);

        return (file.type == VALUE_STRING)
            && (sN(file) == strlen(mod->path))
            && (memcmp(ss(file), mod->path, sN(file)) == 0);
}

bool
TyErrorIsKind(Ty *ty, Value const *v, char const *kind)
{
        if (!TyIsCompileError(v)) {
                return false;
        }

        Value k = MemberStr(ty, v, NAMES._kind);

        return vs_eq_z(k, kind);
}

static void
RenderRuntime(Ty *ty, byte_vector *out, Value const *exc, Value const *detail)
{
        if (
                (detail != NULL)
             && (detail->type == VALUE_STRING)
             && (sN(*detail) > 0)
        ) {
                dump(out, "%.*s\n", (int)sN(*detail), ss(*detail));
        }

        dump(
                out,
                "%sRuntimeError%s: uncaught exception: %s",
                TERM(91;1),
                TERM(0),
                VSC(exc)
        );
}

static void
RenderCause(Ty *ty, byte_vector *out, Value const *cause, Value const *detail)
{
        if (TyIsCompileError(cause)) {
                Value what = Member(ty, cause, NAMES._what);
                if (what.type == VALUE_STRING) {
                        dump(out, "%.*s", (int)sN(what), ss(what));
                }
        } else {
                RenderRuntime(ty, out, cause, detail);
        }
}

Value
TyNewCompileError(
        Ty *ty,
        char const *kind,
        char const *msg,
        Value locs,
        char const *text,
        Value cause,
        Value detail
)
{
        byte_vector what = {0};
        bool wrapped = (cause.type != VALUE_ZERO) && (cause.type != VALUE_NIL);

        GC_STOP();

        if (wrapped) {
                RenderCause(ty, &what, &cause, &detail);
                dump(&what, "\n");
        }

        dump(&what, "%s", (text != NULL) ? text : msg);

        Value err = RawObject(CLASS_COMPILE_ERROR);
        PutMember(err, NAMES._what,    vSs(vv(what), vN(what)));
        PutMember(err, NAMES._ctx,     NIL);
        PutMember(err, NAMES._cause,   wrapped ? cause : NIL);
        PutMember(err, NAMES._kind,    vSsz(kind));
        PutMember(err, NAMES._msg,     vSsz(msg));
        PutMember(err, NAMES._locs,    (locs.type == VALUE_ARRAY) ? locs : ARRAY(vA()));
        PutMember(err, NAMES._detail,  (detail.type == VALUE_STRING) ? detail : NIL);
        PutMember(err, NAMES._related, NIL);

        GC_RESUME();

        xvF(what);

        return err;
}

static Value
VWrapError(
        Ty *ty,
        Value cause,
        Value detail,
        Expr const *where,
        char const *fmt,
        va_list ap
)
{
        byte_vector msg  = {0};
        byte_vector text = {0};

        vdump(&msg, fmt, ap);

        byte_vector heading = {0};
        dump(&heading, "while %s", vv(msg));
        WriteDiagnostic(ty, &text, "note", vv(heading), where, NULL, NULL, 1, 1);
        xvF(heading);

        GC_STOP();

        Value locs = ARRAY(vA());

        Expr const *origin = (where != NULL) ? where->origin : NULL;

        if (origin != NULL && origin->start.s != NULL) {
                vAp(locs.array, TyTraceEntryFor(ty, origin));
        }

        if (where != NULL && where->start.s != NULL) {
                vAp(locs.array, TyTraceEntryFor(ty, where));
        }

        char kind[64] = "CompileError";

        if (TyIsCompileError(&cause)) {
                Value k = MemberStr(ty, &cause, NAMES._kind);
                ty_snprintf(kind, sizeof kind, "%.*s", (int)sN(k), ss(k));
        }

        Value err = TyNewCompileError(
                ty,
                kind,
                vv(msg),
                locs,
                vv(text),
                cause,
                detail
        );

        GC_RESUME();

        xvF(msg);
        xvF(text);

        return err;
}

Value
TyWrapError(
        Ty *ty,
        Value cause,
        Value detail,
        Expr const *where,
        char const *fmt,
        ...
)
{
        va_list ap;

        va_start(ap, fmt);
        Value err = VWrapError(ty, cause, detail, where, fmt, ap);
        va_end(ap);

        return err;
}

Value
TyCatchWrap(Ty *ty, Expr const *where, char const *fmt, ...)
{
        va_list ap;
        Value detail;

        GC_STOP();

        Value cause = TyCatchDetail(ty, &detail);

        va_start(ap, fmt);
        Value err = VWrapError(ty, cause, detail, where, fmt, ap);
        va_end(ap);

        GC_RESUME();

        return err;
}

inline static usize
xmemspn(char const *s, usize n)
{
        char const *nl = memchr(s, '\n', n);
        return (nl == NULL) ? n : (usize)(nl - s);
}

static void
FirstLine(byte_vector *out, char const *s)
{
        usize n = strcspn(s, "\n");
        dump(out, "%.*s", (int)n, s);
}

static void
RenderBrief(Ty *ty, byte_vector *out, Value const *exc)
{
        if (!TyIsCompileError(exc)) {
                FirstLine(out, VSC(exc));
                return;
        }

        Value kind  = MemberStr(ty, exc, NAMES._kind);
        Value msg   = MemberStr(ty, exc, NAMES._msg);
        Value cause = Member(ty, exc, NAMES._cause);

        if (cause.type == VALUE_NIL) {
                dump(out, "%.*s: ", (int)sN(kind), ss(kind));
        } else {
                dump(out, "while ");
        }

        dump(out, "%.*s", (int)xmemspn((char *)ss(msg), sN(msg)), ss(msg));

        Value locs = Member(ty, exc, NAMES._locs);
        if (locs.type == VALUE_ARRAY && vN(*locs.array) > 0) {
                Value loc = v__(*locs.array, 0);
                Value mod = tget_or(&loc, "module", NIL);
                Value *start = tget_nn(&loc, "start");
                if (start != NULL) {
                        dump(
                                out,
                                " %s(%.*s:%d:%d)%s",
                                TERM(90),
                                (mod.type == VALUE_STRING) ? (int)sN(mod) : 1,
                                (mod.type == VALUE_STRING) ? (char *)ss(mod) : "?",
                                (int)tget_or(start, "line", INTEGER(0)).z,
                                (int)tget_or(start, "col", INTEGER(0)).z,
                                TERM(0)
                        );
                }
        }

        if (cause.type != VALUE_NIL) {
                dump(out, " <- ");
                RenderBrief(ty, out, &cause);
        }
}

void
TyErrorBrief(Ty *ty, Value const *exc, byte_vector *out)
{
        RenderBrief(ty, out, exc);
        xvP(*out, '\0');
        vN(*out) -= 1;
}

void
TyFormatError(Ty *ty, Value const *exc, Value const *detail, byte_vector *out)
{
        switch (exc->type) {
        case VALUE_ZERO:
                dump(out, "no error");
                return;
        }

        if (!TyIsCompileError(exc)) {
                RenderRuntime(ty, out, exc, detail);
                return;
        }

        if (
                (detail != NULL)
             && (detail->type == VALUE_STRING)
             && (sN(*detail) > 0)
        ) {
                dump(out, "%.*s\n", (int)sN(*detail), ss(*detail));
        }

        RenderCause(ty, out, exc, NULL);

        Value related = Member(ty, exc, NAMES._related);
        if (related.type != VALUE_ARRAY) {
                return;
        }

        for (usize i = 0; i < vN(*related.array); ++i) {
                Value entry = v__(*related.array, i);
                dump(
                        out,
                        "\n%s%snote%s: %.*s: ",
                        TERM(1),
                        TERM(34),
                        TERM(0),
                        (int)sN(entry.items[0]),
                        ss(entry.items[0])
                );
                RenderBrief(ty, out, &entry.items[1]);
        }
}

static void
PlainChain(Ty *ty, byte_vector *out, Value const *exc)
{
        if (!TyIsCompileError(exc)) {
                FirstLine(out, VSC(exc));
                return;
        }

        Value kind  = MemberStr(ty, exc, NAMES._kind);
        Value msg   = MemberStr(ty, exc, NAMES._msg);
        Value cause = Member(ty, exc, NAMES._cause);

        if (cause.type == VALUE_NIL) {
                dump(out, "%.*s: %.*s", (int)sN(kind), ss(kind), (int)sN(msg), ss(msg));
        } else {
                dump(out, "while %.*s: ", (int)sN(msg), ss(msg));
                PlainChain(ty, out, &cause);
        }
}

static void
CollectLocs(Ty *ty, Array *out, Value const *exc)
{
        if (!TyIsCompileError(exc)) {
                return;
        }

        Value locs = Member(ty, exc, NAMES._locs);
        if (locs.type == VALUE_ARRAY) {
                for (usize i = 0; i < vN(*locs.array); ++i) {
                        vAp(out, v__(*locs.array, i));
                }
        }

        Value cause = Member(ty, exc, NAMES._cause);
        CollectLocs(ty, out, &cause);
}

static Value
ErrorRecord(Ty *ty, Value const *exc)
{
        byte_vector msg = {0};
        Array *trace = vA();

        int color = ColorOutput;
        ColorOutput = false;
        PlainChain(ty, &msg, exc);
        ColorOutput = color;

        CollectLocs(ty, trace, exc);

        Value record = vTn(
                "message", vSs(vv(msg), vN(msg)),
                "trace",   ARRAY(trace)
        );

        xvF(msg);

        return record;
}

Value
TyErrorRecords(Ty *ty, Value const *exc)
{
        GC_STOP();

        Array *records = vA();

        vAp(records, ErrorRecord(ty, exc));

        Value related = TyIsCompileError(exc)
                      ? Member(ty, exc, NAMES._related)
                      : NIL;

        if (related.type == VALUE_ARRAY) {
                for (usize i = 0; i < vN(*related.array); ++i) {
                        Value entry = v__(*related.array, i);
                        if (TyIsCompileError(&entry.items[1])) {
                                vAp(records, ErrorRecord(ty, &entry.items[1]));
                        }
                }
        }

        GC_RESUME();

        return ARRAY(records);
}

Value
TyErrorMessage(Ty *ty, char const *text)
{
        return TyNewCompileError(ty, "Error", text, NIL, text, NIL, NIL);
}

void
TySetError(Ty *ty, Value exc, Value detail)
{
        ty->error        = exc;
        ty->error_detail = detail;
}

char const *
TyError(Ty *ty)
{
        v0(ty->err);
        TyFormatError(ty, &ty->error, &ty->error_detail, &ty->err);
        xvP(ty->err, '\0');
        vN(ty->err) -= 1;
        return vv(ty->err);
}

Value
TyCatchFail(Ty *ty)
{
        Value detail;

        GC_STOP();
        Value exc = TyCatchDetail(ty, &detail);
        TySetError(ty, exc, TyIsCompileError(&exc) ? NIL : detail);
        GC_RESUME();

        return exc;
}

inline static DiagSink *
TopSink(Ty *ty)
{
        return (vN(ty->sinks) > 0) ? vvL(ty->sinks) : NULL;
}

static bool
SameMessage(Ty *ty, Value const *a, Value const *b)
{
        if (!TyIsCompileError(a) || !TyIsCompileError(b)) {
                return false;
        }

        Value ka = MemberStr(ty, a, NAMES._kind);
        Value kb = MemberStr(ty, b, NAMES._kind);
        Value ma = MemberStr(ty, a, NAMES._msg);
        Value mb = MemberStr(ty, b, NAMES._msg);

        return (sN(ka) == sN(kb))
            && (sN(ma) == sN(mb))
            && (memcmp(ss(ka), ss(kb), sN(ka)) == 0)
            && (memcmp(ss(ma), ss(mb), sN(ma)) == 0);
}

static bool
SameError(Ty *ty, Value const *a, Value const *b)
{
        if (a->type == VALUE_OBJECT && b->type == VALUE_OBJECT && a->object == b->object) {
                return true;
        }

        if (!TyIsCompileError(a) || !TyIsCompileError(b)) {
                return false;
        }

        byte_vector x = {0};
        byte_vector y = {0};

        RenderBrief(ty, &x, a);
        RenderBrief(ty, &y, b);

        bool same = (vN(x) == vN(y)) && (memcmp(vv(x), vv(y), vN(x)) == 0);

        xvF(x);
        xvF(y);

        return same;
}

void
TySuppress(Ty *ty, Value exc, char const *what)
{
        if (TraceThrows) {
                byte_vector brief = {0};
                RenderBrief(ty, &brief, &exc);
                fprintf(stderr, "[suppressed: %s] %s\n", what, vv(brief));
                xvF(brief);
        }

        DiagSink *sink = TopSink(ty);
        if (sink == NULL) {
                return;
        }

        for (usize i = 0; i < vN(sink->suppressed); ++i) {
                if (SameError(ty, &v_(sink->suppressed, i)->items[1], &exc)) {
                        return;
                }
        }

        GC_STOP();
        xvP(sink->suppressed, PAIR(vSsz(what), exc));
        GC_RESUME();
}

void
TyDiagPush(Ty *ty, u32 flags)
{
        if (vN(ty->sinks) == 0) {
                v0(ty->diags);
        }

        xvP(ty->sinks, ((DiagSink){ .flags = flags }));
}

bool
TyDiagRecovering(Ty *ty)
{
        DiagSink const *sink = TopSink(ty);

        return (sink != NULL)
            && (sink->flags & DIAG_RECOVER)
            && (EVAL_DEPTH == 0);
}

void
TyDiagRecord(Ty *ty, Value err, Expr const *node)
{
        if (!TyDiagRecovering(ty)) {
                vm_throw(ty, &err);
        }

        DiagSink *sink = TopSink(ty);

        xvP(sink->errors, err);
        xvP(sink->nodes, node);
}

Value
TyDiagFindPoison(Ty *ty, Expr const *e)
{
        for (isize i = vN(ty->sinks) - 1; i >= 0; --i) {
                DiagSink const *sink = v_(ty->sinks, i);
                for (usize j = 0; j < vN(sink->nodes); ++j) {
                        if (v__(sink->nodes, j) == e) {
                                return v__(sink->errors, j);
                        }
                }
        }

        return NIL;
}

static void
Relate(Ty *ty, Value *related, char const *label, Value const *exc)
{
        for (usize i = 0; i < vN(*related->array); ++i) {
                if (SameError(ty, &v_(*related->array, i)->items[1], exc)) {
                        return;
                }
        }

        vAp(related->array, PAIR(vSsz(label), *exc));
}

static Value
AttachRelated(Ty *ty, DiagSink const *sink, Value primary, Value const *thrown)
{
        if (!TyIsCompileError(&primary)) {
                return primary;
        }

        GC_STOP();

        Value related = Member(ty, &primary, NAMES._related);
        if (related.type != VALUE_ARRAY) {
                related = ARRAY(vA());
        }

        for (usize i = 0; i < vN(sink->errors); ++i) {
                Value const *err = v_(sink->errors, i);
                if (!SameError(ty, err, &primary)) {
                        Relate(ty, &related, "additional error", err);
                }
        }

        if (thrown != NULL && !SameError(ty, thrown, &primary)) {
                Relate(ty, &related, "subsequent error", thrown);
        }

        for (usize i = 0; i < vN(sink->suppressed); ++i) {
                Value const *entry = v_(sink->suppressed, i);
                if (
                        !SameMessage(ty, &entry->items[1], &primary)
                     && (thrown == NULL || !SameMessage(ty, &entry->items[1], thrown))
                ) {
                        char const *label = afmt(
                                "earlier error suppressed (%.*s)",
                                (int)sN(entry->items[0]),
                                ss(entry->items[0])
                        );
                        Relate(ty, &related, label, &entry->items[1]);
                }
        }

        if (vN(*related.array) > 0) {
                PutMember(primary, NAMES._related, related);
        }

        GC_RESUME();

        return primary;
}

Value
TyDiagFail(Ty *ty, Value exc, bool *replaced)
{
        DiagSink sink = vXx(ty->sinks);

        *replaced = (vN(sink.errors) > 0);

        Value primary = *replaced ? v__(sink.errors, 0) : exc;
        Value result = AttachRelated(ty, &sink, primary, &exc);

        xvF(sink.errors);
        xvF(sink.nodes);
        xvF(sink.suppressed);

        return result;
}

Value
TyDiagFinish(Ty *ty)
{
        DiagSink sink = vXx(ty->sinks);
        DiagSink *parent = TopSink(ty);

        Value rep = (vN(sink.errors) > 0)     ? v__(sink.errors, 0)
                  : (vN(sink.suppressed) > 0) ? v_(sink.suppressed, 0)->items[1]
                  : NIL;

        for (usize i = 0; i < vN(sink.errors); ++i) {
                if (parent != NULL) {
                        xvP(parent->errors, v__(sink.errors, i));
                        xvP(parent->nodes, v__(sink.nodes, i));
                } else {
                        xvP(ty->diags, v__(sink.errors, i));
                }
        }

        xvF(sink.errors);
        xvF(sink.nodes);
        xvF(sink.suppressed);

        return rep;
}

void
TyDiagMark(Ty *ty)
{
        value_mark(ty, &ty->error);
        value_mark(ty, &ty->error_detail);

        for (usize i = 0; i < vN(ty->diags); ++i) {
                value_mark(ty, v_(ty->diags, i));
        }

        for (usize i = 0; i < vN(ty->sinks); ++i) {
                DiagSink const *sink = v_(ty->sinks, i);
                for (usize j = 0; j < vN(sink->errors); ++j) {
                        value_mark(ty, v_(sink->errors, j));
                }
                for (usize j = 0; j < vN(sink->suppressed); ++j) {
                        value_mark(ty, v_(sink->suppressed, j));
                }
        }
}

/* vim: set sts=8 sw=8 expandtab: */
