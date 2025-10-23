#include <stdio.h>
#include <stdalign.h>
#include <ctype.h>
#include <string.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>
#include <stdarg.h>
#include <stdnoreturn.h>
#include <unistd.h>

#include "scope.h"
#include "ty.h"
#include "alloc.h"
#include "location.h"
#include "operators.h"
#include "log.h"
#include "util.h"
#include "value.h"
#include "ast.h"
#include "dict.h"
#include "functions.h"
#include "lex.h"
#include "parse.h"
#include "tags.h"
#include "class.h"
#include "vm.h"
#include "compiler.h"
#include "types.h"

#if defined(TY_LS)
 #include "json.h"
#endif

#if defined(TY_PROFILER)
 #include "istat.h"
#endif

#define DT(e, ...) do {                     \
        fprintf(                            \
                stderr,                     \
                "%s:%d: [type(%s) = %s]: ", \
                __func__,                   \
                __LINE__,                   \
                #e,                         \
                type_show(ty, (e))          \
        );                                  \
        fprintf(stderr, "" __VA_ARGS__);    \
        fprintf(stderr, "\n");              \
} while (0)

#undef DT
#define DT(...)

#define emit_instr(i) ((emit_instr)(ty, i))
#define INSNx(i)      ((emit_instr)(ty, i))
#define INSN(i)       ((emit_instr)(ty, INSTR_##i))

#define EE(x)    emit_expression(ty, (x))
#define EM(x)    emit_member(ty, (x))
#define Ei32(x)  emit_int(ty, (x))
#define Eu8(x)   avP(STATE.code, (x))
#define Eu1(x)   avP(STATE.code, !!(x))
#define ES(x, b) emit_statement(ty, (x), (b))
#define EC(x)    emit_constraint(ty, (x))
#define EA(x)    emit_assertion(ty, (x))

#define PLACEHOLDER_JUMP(t, name) JumpPlaceholder name = (PLACEHOLDER_JUMP)(ty, (INSTR_##t))
#define LABEL(name) JumpLabel name = (LABEL)(ty)

#define PLACEHOLDER_JUMP_IF_NOT(e, name) JumpPlaceholder name = (PLACEHOLDER_JUMP_IF_NOT)(ty, (e))
#define PLACEHOLDER_JUMP_IF(e, name)     JumpPlaceholder name = (PLACEHOLDER_JUMP_IF)    (ty, (e))

#define PATCH_OFFSET(i)                                           \
        do {                                                      \
                int dist = vN(STATE.code) - i - sizeof dist;      \
                memcpy(STATE.code.items + i, &dist, sizeof dist); \
        } while (0)

#define PATCH_JUMP(name)                            \
        do {                                        \
                PATCH_OFFSET((name).off);           \
                annotate(":L%d", (name).label + 1); \
        } while (0)

#define JUMP(loc)                                                          \
        do {                                                               \
                annotate("%sL%d%s", TERM(95), (loc).label + 1, TERM(0));   \
                INSN(JUMP);                                                \
                Ei32((loc).off - vN(STATE.code) - sizeof (int));           \
        } while (0)

#define JUMP_IF_NOT(loc)                                                   \
        do {                                                               \
                annotate("%sL%d%s", TERM(95), (loc).label + 1, TERM(0));   \
                INSN(JUMP_IF_NOT);                                         \
                Ei32((loc).off - vN(STATE.code) - sizeof (int));           \
        } while (0)

#define EMIT_GROUP_LABEL(g, s)  \
        annotate(               \
                (g).label == 0  \
              ? s               \
              : s "%d",         \
                (g).label + 1   \
        );

#define FAIL_MATCH_IF(instr)                                 \
        do{                                                  \
                EMIT_GROUP_LABEL(STATE.match_fails, "Fail"); \
                INSN(instr);                                 \
                avP(STATE.match_fails, vN(STATE.code));      \
                Ei32(0);                                     \
        } while (0)

#define CHECK_INIT() if (CheckTypes) { INSN(CHECK_INIT); }

#define SET_TYPE_SRC(e) ((e) != NULL && (e)->_type != NULL && ((e)->_type->src = (Expr *)(e)))

#define NO_TYPES (!CheckTypes || TY_IS_READY)

#define RUNTIME_CONSTRAINTS CheckConstraints

#if defined(TY_PROFILER) || 1
#define KEEP_LOCATION(e) true
#else
#define KEEP_LOCATION(e) ((e)->type > EXPRESSION_KEEP_LOC)
#endif

#if 0
  #define INSTR_SAVE_STACK_POS INSTR_SAVE_STACK_POS), Ei32(__LINE__
  #define INSTR_POP_STACK_POS INSTR_POP_STACK_POS), Ei32(__LINE__
#endif

#define CurrentClassID ((STATE.class != NULL) ? (STATE.class->i) : -1)
#define SCOPE (*vvL(STATE.scopes))
#define PushScope(scope) xvP(STATE.scopes, (scope))
#define PopScope()       vvX(STATE.scopes)

#define ScopeLookupEx(scope, name, flags)                   \
        scope_xlookup(                                      \
                ty,                                         \
                (scope),                                    \
                (name),                                     \
                (                                           \
                        (flags)                             \
                      | (SCOPE_PERMISSIVE * !!STATE._based) \
                )                                           \
        )
#define ScopeLookupLocalEx(scope, name, flags)                       \
        ScopeLookupEx((scope), (name), ((flags) | SCOPE_LOCAL_ONLY))

#define ScopeLookupLocal(scope, name)          \
        ScopeLookupLocalEx((scope), (name), 0)

#define ScopeLookup(scope, name) ScopeLookupEx((scope), (name), 0)


#define WITH_STATE_N_2(prop, val) for (                      \
        struct {                                             \
                typeof (STATE.prop) save;                    \
                bool cond;                                   \
        } _st_ctx = { STATE.prop, 1 };                       \
        (                                                    \
                (_st_ctx.cond && ((STATE.prop = (val)), 1))  \
             || ((STATE.prop = _st_ctx.save), 0)             \
        );                                                   \
        _st_ctx.cond = 0                                     \
)

#define WITH_STATE_N_4(p1, v1, p2, v2)  \
        WITH_STATE_N_2(p1, (v1))        \
        WITH_STATE_N_2(p2, (v2))

#define WITH_STATE_N_6(p1, v1, p2, v2, p3, v3)  \
        WITH_STATE_N_2(p1, (v1))                \
        WITH_STATE_N_2(p2, (v2))                \
        WITH_STATE_N_2(p3, (v3))

#define WITH_STATE(...) VA_SELECT(WITH_STATE_N, __VA_ARGS__)

#define WITH_SCOPE_LIMIT(t) // TODO we don't need this
#define WITH_PERMISSIVE_SCOPE WITH_STATE(_based, 1)

#define WITH_SELF(x) WITH_STATE(self, ((x) != NULL) ? (x) : STATE.self)

#define WITH_EXPECTED_TYPE(x) WITH_STATE(expected_type, (x))

enum { CTX_EXPR, CTX_TYPE };
#define WITH_CTX(c) WITH_STATE(ctx, CTX_##c)
#define IS_CTX(c) (STATE.ctx == (CTX_##c))


bool SuggestCompletions = false;
bool FindDefinition = false;
int QueryLine;
int QueryCol;
char const *QueryFile;
Symbol const *QueryResult;
Expr const *QueryExpr;

bool ProduceAnnotation = true;
usize GlobalCount = 0;

static int builtin_modules;
static int BuiltinCount;

static CompileState STATE;
#define STATE STATE

static vec(Module *) modules;
static vec(ProgramAnnotation) annotations;
static vec(location_vector) location_lists;
static vec(Expr const *) source_map;
static JumpGroup PreludeAssertionOffsets;
static Module *MainModule;
static Module *GlobalModule;
static Scope *GlobalScope;
static Symbol *AnyTypeSymbol;
static Scope *ThreadLocals;
static u64 t;
static char const EmptyString[] = "\0";
static char const UnknownString[] = "\0(unknown location)";
static Location Nowhere = { 0, 0, 0, EmptyString + 1 };
static Location UnknownStart = { 0, 0, 0, UnknownString + 1 };
static Location UnknownEnd = { 0, 0, 0, UnknownString + sizeof UnknownString - 1 };
static Symbol UndefinedSymbol = { .flags = SYM_PUBLIC | SYM_GLOBAL, .i = -1 };

typedef struct context_entry ContextEntry;

struct context_entry {
        ContextEntry *next;
        char const *info;
        Expr *e;
};

static ContextEntry *ContextList;

static Module *
GetModule(Ty *ty, char const *name);

static Module *
GetModuleImport(Ty *ty, Module const *mod, char const *name);

static void
symbolize_statement(Ty *ty, Scope *scope, Stmt *s);

static void
symbolize_pattern(Ty *ty, Scope *scope, Expr *e, Scope *reuse, bool def);

static void
symbolize_expression(Ty *ty, Scope *scope, Expr *e);

static void
UpdateRefinemenets(Ty *ty, Scope *scope);

static void
AddRefinements(Ty *ty, Expr const *e, Scope *_then, Scope *_else);

static bool
emit_statement(Ty *ty, Stmt const *s, bool want_result);

static bool
emit_expression(Ty *ty, Expr const *e);

static bool
emit_expr(Ty *ty, Expr const *e, bool need_loc);

static void
emit_assignment(Ty *ty, Expr *target, Expr const *e, bool maybe, bool def);

static void
emit_assignment2(Ty *ty, Expr *target, bool maybe, bool def);

static bool
emit_case(Ty *ty, Expr const *pattern, Expr const *cond, Stmt const *s, bool want_result);

static bool
emit_catch(Ty *ty, Expr const *pattern, Expr const *cond, Stmt const *s, bool want_result);

inline static void
emit_tgt(Ty *ty, Symbol *s, Scope const *scope, bool def);

static void
emit_return_check(Ty *ty, Expr const *f);

static Scope *
get_import_scope(Ty *ty, char const *);

static Scope *
search_import_scope(char const *);

static void
import_module(Ty *ty, Stmt const *s);

static Scope *
get_module_scope(char const *name);

static void
invoke_fun_macro(Ty *ty, Scope *, Expr *e);

static void
emit_spread(Ty *ty, Expr const *e, bool nils);

static Stmt **
compile(Ty *ty, char const *source);

inline static void
emit_int(Ty *ty, int k);

static bool
try_make_implicit_self(Ty *ty, Expr *e, int class);

static void
RedpillFun(Ty *ty, Scope *scope, Expr *f, Type *self0);

static void
InjectRedpill(Ty *ty, Stmt *s);

static void
DeclareSymbols(Ty *ty, Stmt *stmt);

static void
DefinePending(Ty *ty);

static void
AddClassTraits(Ty *ty, ClassDefinition const *def);

static void
ResolveFieldTypes(Ty *ty, Scope *scope, expression_vector const *fields);

static bool
expedite_fun(Ty *ty, Expr *e, void *ctx);

static RangeLoop
BeginRangeLoop(
        Ty *ty,
        i32 n,
        bool want_result,
        Expr *range,
        Expr *target
);

static void
CheckRangeLoop(Ty *ty, RangeLoop *loop, Expr *_while, Expr *_if);

static void
EndRangeLoop(Ty *ty, RangeLoop *loop);

#define X(t) #t
static char const *ExpressionTypeNames[] = {
        TY_EXPRESSION_TYPES
};
static char const *StatementTypeNames[] = {
        TY_STATEMENT_TYPES
};
#undef X

static void
dumpstr(byte_vector *out, char const *s)
{
#define COLOR(i) xvPn(*out, TERM(i), strlen(TERM(i)))

        COLOR(92);

        xvP(*out, '\'');

        if (s != NULL) for (char const *c = s; *c != '\0'; ++c) switch (*c) {
        case '\t':
                COLOR(95);
                xvP(*out, '\\');
                xvP(*out, 't');
                COLOR(92);
                break;

        case '\r':
                COLOR(95);
                xvP(*out, '\\');
                xvP(*out, 'r');
                COLOR(92);
                break;

        case '\n':
                COLOR(95);
                xvP(*out, '\\');
                xvP(*out, 'n');
                COLOR(92);
                break;

        case '\\':
                COLOR(95);
                xvP(*out, '\\');
                xvP(*out, '\\');
                COLOR(92);
                break;

        case '\'':
                COLOR(95);
                xvP(*out, '\\');
                xvP(*out, '\'');
                COLOR(92);
                break;

        default:
                xvP(*out, *c);
        }

        xvP(*out, '\'');

        COLOR(0);

#undef COLOR

        xvP(*out, '\0');
        vvX(*out);
}

#define annotate(...)                                                        \
        if (ProduceAnnotation) do {                                          \
                xvP(                                                         \
                        STATE.annotation.map,                                \
                        (void const *)(uptr)vN(STATE.code)                   \
                );                                                           \
                xvP(                                                         \
                        STATE.annotation.captions,                           \
                        (void const *)(uptr)vN(STATE.annotation.text)        \
                );                                                           \
                dump(&STATE.annotation.text, __VA_ARGS__);                   \
                xvP(STATE.annotation.text, '\0');                            \
        } while (0)

static void
PatchAnnotation(ProgramAnnotation *annotation, void const *base)
{
        for (int i = 0; i < vN(annotation->map); ++i) {
                v__(annotation->map, i) = (void const *)(
                                (uptr)v__(annotation->map, i)
                              + (uptr)base
                );
        }

        for (int i = 0; i < vN(annotation->captions); ++i) {
                v__(annotation->captions, i) = (void const *)(
                                (uptr)v__(annotation->captions, i)
                              + (uptr)vv(annotation->text)
                );
        }

        annotation->start += (uptr)base;
        annotation->end += (uptr)base;

        annotation->patched = true;
}

inline static char const *
CurrentModuleName(Ty *ty)
{
        return (STATE.module != NULL) ? STATE.module->name : NULL;
}

inline static char const *
CurrentModulePath(Ty *ty)
{
        return (STATE.module != NULL) ? STATE.module->path : NULL;
}

inline static Expr *
NewExpr(Ty *ty, int t)
{
        Expr *e = amA0(sizeof *e);
        e->arena = GetArenaAlloc(ty);
        e->start = UnknownStart;
        e->end = UnknownEnd;
        e->mod = STATE.module;
        e->type = t;
        return e;
}

inline static Stmt *
NewStmt(Ty *ty, int t)
{
        Stmt *s = amA0(sizeof *s);
        s->arena = GetArenaAlloc(ty);
        s->start = UnknownStart;
        s->end = UnknownEnd;
        s->mod = STATE.module;
        s->type = t;
        return s;
}

inline static int
tag_app_tag(Expr const *e)
{
        if (e->identifier == EmptyString) {
                return e->constraint->v->tag;
        } else {
                return e->symbol->tag;
        }
}

inline static int
wrapped_type(Ty *ty, Value const *v)
{
        if (v->tags == 0 || tags_pop(ty, v->tags) == 0) {
                return v->type & ~VALUE_TAGGED;
        } else {
                return v->type;
        }
}

inline static bool
has_any_names(Expr const *e)
{
        for (int i = 0; i < vN(e->names); ++i) {
                if (v__(e->names, i) != NULL) {
                        return true;
                }
        }

        return false;
}

inline static bool
HasBody(Expr const *fun)
{
        if (fun == NULL) {
                return false;
        }

        switch (fun->type) {
        case EXPRESSION_FUNCTION:
                return fun->body != NULL;

        case EXPRESSION_MULTI_FUNCTION:
                for (int i = 0; i < vN(fun->functions); ++i) {
                        if (HasBody(v__(fun->functions, i))) {
                                return true;
                        }
                }
                return false;
        }

        return false;
}

inline static bool
IsClassName(Expr const *expr)
{
        return (expr->type == EXPRESSION_IDENTIFIER)
            && (expr->symbol != NULL)
            && (expr->symbol->class != -1);
}

inline static bool
IsLocalMemberSymbol(Ty *ty, Symbol const *sym, Scope const *scope)
{
        return SymbolIsMember(sym)
            && (STATE.class != NULL)
            && (STATE.self->scope->function == scope->function)
            && (STATE.meth->mtype != MT_2OP);
}

inline static bool
IsLocalMember(Ty *ty, Expr const *expr, Scope const *scope)
{
        return (expr != NULL)
            && (expr->type == EXPRESSION_IDENTIFIER)
            && (expr->symbol != NULL)
            && IsLocalMemberSymbol(ty, expr->symbol, scope);
}

inline static bool
IsSimpleRange(Expr const *expr)
{
        if (
                (expr->type == EXPRESSION_MEMBER_ACCESS)
             && (strcmp(expr->member->identifier, "rev") == 0)
        ) {
                expr = expr->object;
        }

        return (expr->type == EXPRESSION_DOT_DOT)
            || (expr->type == EXPRESSION_DOT_DOT_DOT);
}

inline static bool
IsRangeLoop(Stmt const *loop)
{
        return (loop->type == STATEMENT_EACH_LOOP)
            && IsSimpleRange(loop->each.array);

}

inline static bool
IsPrivateMember(char const *name)
{
        usize n = strlen(name);
        return (n > 2)
            && (name[0] == '_')
            && (name[1] == '_')
            && (
                        (name[n - 1] != '_')
                     || (name[n - 2] != '_')
               )
            ;
}

inline static char *
GetPrivateName(char const *name, int class, char *scratch, usize n)
{
        if (IsPrivateMember(name) && class >= 0) {
                snprintf(scratch, n, "%s$%d", &name[2], class);
                return scratch;
        } else {
                return (char *)name;
        }
}

static void
emit_member(Ty *ty, char const *name)
{
        char scratch[512];

        char const *private = GetPrivateName(
                name,
                CurrentClassID,
                scratch,
                sizeof scratch
        );

        Ei32(M_ID(private));
}

static bool
QualifiedName_(Expr const *e, byte_vector *b)
{
        if (e == NULL) {
                return true;
        }

        bool good = true;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                good &= QualifiedName_(e->namespace, b);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                good &= QualifiedName_(e->object, b);
                break;
        case EXPRESSION_MODULE:
        case EXPRESSION_NAMESPACE:
                good &= QualifiedName_(e->parent, b);
                break;
        default:
                return false;
        }

        if (b->count > 0) {
                xvP(*b, '.');
        }

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                for (char const *m = e->module; m && *m; ++m) {
                        xvP(*b, *m == '/' ? '.' : *m);
                }
                xvPn(*b, e->identifier, strlen(e->identifier));
                break;
        case EXPRESSION_MEMBER_ACCESS:
                xvPn(*b, e->member->identifier, strlen(e->member->identifier));
                break;
        case EXPRESSION_MODULE:
        case EXPRESSION_NAMESPACE:
                xvPn(*b, e->name, strlen(e->name));
                break;
        }

        return true;
}

static char const *
QualifiedName(Expr const *e)
{
        _Thread_local static byte_vector name = {0};

        vN(name) = 0;

        if (QualifiedName_(e, &name)) {
                xvP(name, '\0');
                return vv(name);
        } else {
                return "(error)";
        }
}

inline static bool
IsStmt(Expr const *expr)
{
        return (expr->type > STATEMENT_TYPE_START);
}

char const *
ExpressionTypeName(Expr const *e)
{
        if (e == NULL) {
                return "(null)";
        }

        if (e->type == EXPRESSION_STATEMENT) {
                if (e->statement->type == STATEMENT_EXPRESSION) {
                        return ExpressionTypeName(e->statement->expression);
                } else {
                        return StatementTypeNames[e->statement->type - (STATEMENT_TYPE_START + 1)];
                }
        } else if (IsStmt(e)) {
                return StatementTypeNames[e->type - (STATEMENT_TYPE_START + 1)];
        } else {
                return ExpressionTypeNames[e->type];
        }
}

Module *
GetScopeModule(Ty *ty, Scope const *scope)
{
        for (int i = 0; i < vN(modules); ++i) {
                Module const *mod = v__(modules, i);
                if (
                        (mod != GlobalModule)
                     && ScopeIsContainedBy(scope, mod->scope)
                ) {
                        return (Module *)mod;
                }
        }

        return GlobalModule;
}

Module *
ExpressionModule(Expr const *e)
{
        return (e != NULL) ? e->mod : NULL;
}

char const *
GetExpressionModule(Expr const *e)
{
        Module *mod = ExpressionModule(e);
        return (mod != NULL) ? mod->name : "(unknown)";
}

void
colorize_code(
        char const *expr_color,
        char const *base_color,
        Location const *start,
        Location const *end,
        char *out,
        usize n
)
{
        char const *prefix = start->s;
        char const    *eol = start->s + strcspn(start->s, "\n");
        char const *suffix = (eol > end->s) ? end->s : eol;

        while (prefix[-1] != '\0' && prefix[-1] != '\n')
                --prefix;

        while (isspace(prefix[0]))
                ++prefix;

        int before = start->s - prefix;
        int length = suffix - start->s;
        int after = strcspn(suffix, "\n");

        if (length == 0) {
                length = 1;
                suffix += 1;
        }

        bool color = *base_color != '\0';

        snprintf(
                out,
                n == 0 ? 0 : n - 1,
                "%s%.*s%s%s%.*s%s%s%.*s%s",
                base_color,
                before,
                prefix,
                color ? TERM(1) : "",
                expr_color,
                length,
                start->s,
                color ? TERM(0) : "",
                base_color,
                after,
                suffix,
                color ? TERM(0) : ""
        );
}

void
colorize_code_multiline(
        char const *expr_color,
        char const *base_color,
        Location const *start,
        Location const *end,
        byte_vector *buf
)
{
        char const *ls = start->s, *le = end->s + strcspn(end->s, "\n");
        char const *p, *q;
        usize min = SIZE_MAX, indent, skip;
        bool color = *base_color != '\0', hi = false;

        while (ls[-1] != '\0' && ls[-1] != '\n') {
                --ls;
        }

        for (p = ls; p <= le;) {
                if (p > ls && p[-1] == '\n') {
                        for (indent = 0, q = p; q < le && isspace(*q) && *q != '\n';) {
                                ++indent, ++q;
                        }
                        if (q < le && *q != '\n' && indent < min) {
                                min = indent;
                        }
                }
                p += *p == '\n' ? 1 : strcspn(p, "\n");
        }

        for (indent = 0; ls[indent] && isspace(ls[indent]) && ls[indent] != '\n';) {
                ++indent;
        }
        if (indent < min) {
                min = indent;
        }
        if (min == SIZE_MAX) {
                min = 0;
        }

        for (p = ls; p <= le;) {
                if (p == ls || p[-1] == '\n') {
                        for (skip = 0; skip < min && isspace(p[skip]) && p[skip] != '\n';) {
                                ++skip;
                        }
                        p += skip;
                }

                if (p == start->s && !hi) {
                        if (color) {
                                dump(buf, "%s%s", TERM(1), expr_color);
                        } else {
                                dump(buf, "%s", expr_color);
                        }
                        hi = true;
                }

                if (p == end->s && hi) {
                        if (color) {
                                dump(buf, "%s%s", TERM(0), base_color);
                        }
                        hi = false;
                }

                xvP(*buf, *p);
                ++p;
        }

        if (color && hi) {
                dump(buf, "%s", TERM(0));
        }
}

char *
ContextString(Ty *ty)
{
        char buffer[1024];
        int i = 0;

        ContextEntry *ctx = ContextList;

        while (ctx != NULL) {
                i += sprintf(buffer + i, "%p[%p]%s", ctx, ctx->e, ctx->next == NULL ? "\n" : " -> ");
                ctx = ctx->next;
        }

        return sclone(ty, buffer);
}

static void *
PushContext(Ty *ty, void const *ctx)
{
        if (ContextList != NULL && ContextList->e == ctx) {
                return ContextList;
        }

        ContextEntry *new = amA(sizeof *new);
        new->next = ContextList;
        new->info = NULL;
        new->e = (void *)ctx;

        SWAP(ContextEntry *, new, ContextList);

        //printf("PushContext(%s) -> %p: depth=%d\n", ExpressionTypeName(ctx), ContextList, CompilationDepth(ty));

        return (void *)new;
}

static void
CloneContext(Ty *ty)
{
        //printf("Clone(%s): depth=%d\n", ExpressionTypeName(ContextList->e), CompilationDepth(ty));

        if (ContextList->e->type > EXPRESSION_MAX_TYPE) {
                Stmt *new = amA(sizeof *new);
                *new = *(Stmt *)ContextList->e;
                ContextList->e = (Expr *)new;
        } else {
                Expr *new = amA(sizeof *new);
                *new = *ContextList->e;
                ContextList->e = new;
        }
}

inline static void *
RestoreContext(Ty *ty, void *ctx)
{
        SWAP(void *, ContextList, ctx);
        return ctx;
}

void *
GetCompilerContext(Ty *ty)
{
        return ContextList;
}

void
SetCompilerContext(Ty *ty, void *ctx)
{
        ContextList = ctx;
}

static void *
PushInfo(Ty *ty, void const *ctx, char const *fmt, ...)
{
        char buffer[1024];
        va_list ap;

        va_start(ap, fmt);
        vsnprintf(buffer, sizeof buffer, fmt, ap);
        va_end(ap);

        void *save = PushContext(ty, ctx);
        ContextList->info = sclonea(ty, buffer);

        return save;
}

#define fail(...) CompileError(ty, __VA_ARGS__)
#define fail_or(...) if (!AllowErrors || EVAL_DEPTH > 0) { CompileError(ty, __VA_ARGS__); } else
noreturn void
CompileError(Ty *ty, char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        v0(ErrorBuffer);

        dump(&ErrorBuffer, "%s%sCompileError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        vdump(&ErrorBuffer, fmt, ap);

        va_end(ap);


#if defined(TY_LS)
        Value msg = vSsz(vv(ErrorBuffer));
        Value trace = (CompilationDepth(ty) > 0) ? CompilationTraceArray(ty) : ARRAY(vA());
        Value record = vTn("message", msg, "trace", trace);
        v0(ErrorBuffer);
        json_dump(ty, &record, &ErrorBuffer);
        xvP(ErrorBuffer, '\0');
#else
        if (CompilationDepth(ty) > 0) {
                dump(&ErrorBuffer, "\n");
                CompilationTrace(ty, &ErrorBuffer);
        }
#endif

        ContextList = NULL;

#if 0
        if (vN(ty->jbs) < 3) {
                fputs(TyError(ty), stdout);
                *(char *)0 = 0;
        }
#endif

        TY_THROW_ERROR();
}

void *
CompilerPushContext(Ty *ty, void const *ctx)
{
        return PushContext(ty, ctx);
}

static int
eloc_cmp(void const *a_, void const *b_)
{
        struct eloc const *a = a_;
        struct eloc const *b = b_;

        if (a->p_start < b->p_start) return -1;
        if (a->p_start > b->p_start) return  1;

        return 0;
}

#define edbg(e) ((edbg)(ty, (e)))
static char *
(edbg)(Ty *ty, Expr const *e)
{
        Value v = tyexpr(ty, e);
        return VSC(&v);
}

char const *
show_expr_type(Ty *ty, Expr const *e)
{
        Value v = tyexpr(ty, e);

        if (v.type == VALUE_TAG) {
                return tags_name(ty, v.tag);
        } else {
                return tags_name(ty, tags_first(ty, v.tags));
        }
}

char *
show_expr(Expr const *e)
{
        char buffer[4096];
        colorize_code(TERM(93), TERM(0), &e->start, &e->end, buffer, sizeof buffer);
        return S2(buffer);
}

char *
show_expr_full(Expr const *e)
{
        byte_vector buffer = {0};
        colorize_code_multiline(TERM(93), TERM(0), &e->start, &e->end, &buffer);
        return vv(buffer);
}

static void
dump_source_of(Expr const *e, byte_vector *out)
{
        ptrdiff_t n = e->end.s - e->start.s;

        if (n > 0) {
                xvPn(*out, e->start.s, n);
        } else {
                xvPn(*out, "(it's over)", 11);
        }

}

static void
ProposeMemberDefinition(Ty *ty, Location start, Location end, Expr const *o, char const *m)
{
        if (
                (start.line == QueryLine)
             && (start.col  <= QueryCol)
             && (
                     (end.col  >= QueryCol)
                  || (end.line >  QueryLine)
                )
             && strcmp(CurrentModulePath(ty), QueryFile) == 0
        ) {
                static Symbol sym;

                sym = (Symbol) {
                        .identifier = m,
                        .loc = Nowhere,
                        .mod = STATE.module,
                        .doc = "",
                        .type = NULL
                };

                Type *t0 = type_member_access_t(ty, o->_type, m, false);
                Expr const *member = type_find_member(ty, o->_type, m);
                char const *name = NULL;
                char const *doc = NULL;

                if (member != NULL) {
                        if (
                                (member->type == EXPRESSION_FUNCTION)
                             || (member->type == EXPRESSION_MULTI_FUNCTION)
                        ) {
                                name = member->name;
                                if (member->fn_symbol != NULL) {
                                        doc = member->doc;
                                } else {
                                        doc = member->symbol->doc;
                                }
                        } else if (member->type == EXPRESSION_TUPLE) {
                                for (int i = 0; i < vN(member->es); ++i) {
                                        char const *name_i = v__(member->names, i);
                                        if (name_i != NULL && strcmp(name_i, m) == 0) {
                                                name = name_i;
                                                member = v__(member->es, i);
                                                doc = show_expr_full(member);
                                                break;
                                        }
                                }
                        } else if (
                                (member->type == EXPRESSION_IDENTIFIER)
                             && (member->symbol != NULL)
                        ) {
                                name = member->symbol->identifier;
                                doc = member->symbol->doc;
                        }
                        sym = (Symbol) {
                                .identifier = name,
                                .loc = member->start,
                                .mod = member->mod,
                                .doc = doc,
                                .type = t0
                        };
                        QueryResult = &sym;
                } else if (t0 != NULL) {
                        sym.type = t0;
                        QueryResult = &sym;
                }
        }
}

static bool
WillReturn(void const *_e)
{
        Expr const *e = _e;

        if (e == NULL) {
                return false;
        }

        if (e->type > EXPRESSION_MAX_TYPE) {
                return ((Stmt const *)e)->will_return;
        }

        bool ret;

        switch (e->type) {
        case EXPRESSION_STATEMENT:
                return e->statement->will_return;

        case EXPRESSION_CONDITIONAL:
                return WillReturn(e->then)
                    && WillReturn(e->otherwise);

        case EXPRESSION_WITH:
                return e->with.block->will_return;

        case EXPRESSION_MATCH:
                ret = vN(e->thens) > 0;
                for (int i = 0; ret && i < vN(e->thens); ++i) {
                        ret &= WillReturn(v__(e->thens, i));
                }
                return ret;
        }

        return false;
}

static i32
ResolveClassSpec(Ty *ty, Expr const *spec)
{
        i32 c;

Restart:
        switch (spec->type) {
        case EXPRESSION_MATCH_ANY:
                return CLASS_OBJECT;

        case EXPRESSION_FUNCTION:
        case EXPRESSION_FUNCTION_TYPE:
                return CLASS_FUNCTION;

        case EXPRESSION_NIL:
                return CLASS_NIL;

        case EXPRESSION_IDENTIFIER:
                if (spec->symbol == NULL) {
                        goto Sorry;
                }
                if (
                        (c = spec->symbol->class) < 0
                     && (spec->symbol != AnyTypeSymbol)
                     && !SymbolIsTypeVar(spec->symbol)
                ) {
                        goto Sorry;
                }
                break;

        case EXPRESSION_SUBSCRIPT:
                spec = spec->container;
                goto Restart;

        default:
                c = type_approx_class(type_resolve(ty, spec));
                if (c < 0) {
Sorry:
                        PushContext(ty, spec);
                        fail("not a valid class specifier");
                }
        }

        return c;
}

static Type *
ResolveConstraint(Ty *ty, Expr *constraint)
{
        if (constraint == NULL || !CheckTypes) {
                return NULL;
        }

        Type *t0 = type_fixed(ty, type_resolve(ty, constraint));

        // XXX
        if (1 && (t0 != NULL)) {
                constraint->type = EXPRESSION_TYPE;
                constraint->_type = t0;
        }

        return t0;
}

inline static void
(emit_instr)(Ty *ty, int c)
{
        static int last0 = -1;
        static int last1 = -1;
        static int last2 = -1;
        static int last3 = -1;

        // XXX please do better
        if (
                (last0 == INSTR_SAVE_STACK_POS)
             && (last1 == INSTR_TARGET_LOCAL)
             && (last2 == INSTR_ASSIGN)
             && (last3 == INSTR_POP_STACK_POS)
             &&     (c == INSTR_POP)
        ) {
                int i;

                vvX(STATE.code); // POP_STACK_POS
                vvX(STATE.code); // ASSIGN
                memcpy(&i, vZ(STATE.code) - sizeof i, sizeof i);
                vN(STATE.code) -= sizeof i;
                vvX(STATE.code); // TARGET_LOCAL
                vvX(STATE.code); // SAVE_STACK_POS

                avP(STATE.code, INSTR_ASSIGN_LOCAL);
                Ei32(i);

                last0 = -1;
                last1 = -1;
                last2 = -1;
                last3 = INSTR_ASSIGN_LOCAL;
        } else if (
                last2 == INSTR_TARGET_LOCAL
             && last3 == INSTR_ASSIGN
             &&     c == INSTR_POP
        ) {
                int i;

                vvX(STATE.code); // ASSIGN
                memcpy(&i, vZ(STATE.code) - sizeof i, sizeof i);
                vN(STATE.code) -= sizeof i;
                vvX(STATE.code); // TARGET_LOCAL

                avP(STATE.code, INSTR_ASSIGN_LOCAL);
                Ei32(i);

                last0 = -1;
                last1 = -1;
                last2 = -1;
                last3 = INSTR_ASSIGN_LOCAL;
        } else if (
                last3 == INSTR_TARGET_SUBSCRIPT
             &&     c == INSTR_ASSIGN
        ) {
                *vvL(STATE.code) = INSTR_ASSIGN_SUBSCRIPT;
                last0 = -1;
                last1 = -1;
                last2 = -1;
                last3 = INSTR_ASSIGN_SUBSCRIPT;
        } else {
                avP(STATE.code, (char)c);

                last0 = last1;
                last1 = last2;
                last2 = last3;
                last3 = c;
        }
}

static int
method_cmp(void const *a_, void const *b_)
{
        Expr const *a = *(Expr const **)a_;
        Expr const *b = *(Expr const **)b_;

        int o = (a->name == NULL || b->name == NULL) ? 0 : strcmp(a->name, b->name);

        if (o != 0 && strncmp(a->name, "init#", 5) == 0) { return -1; }
        if (o != 0 && strncmp(b->name, "init#", 5) == 0) { return +1; }

        if (o != 0 && strcmp(a->name, "init") == 0) { return -1; }
        if (o != 0 && strcmp(b->name, "init") == 0) { return +1; }

        return (o != 0) ? o : (a->t - b->t);
}

static char *
try_slurp_module(Ty *ty, char const *name, char const **path_out)
{
        char chadbuf[PATH_MAX + 1];
        char pathbuf[PATH_MAX + 1];

        char const *home = getenv("HOME");

        if (home == NULL) {
                home = getenv("USERPROFILE");
        }

        char *source = NULL;

        if (home != NULL) {
                snprintf(pathbuf, sizeof pathbuf, "%s/.ty/%s.ty", home, name);
                if ((source = slurp(ty, pathbuf)) != NULL) {
                        goto FoundModule;
                }
        }

        if (get_directory_where_chad_looks_for_runtime_dependencies(chadbuf)) {
                snprintf(pathbuf, sizeof pathbuf, "%s/lib/%s.ty", chadbuf, name);
                if ((source = slurp(ty, pathbuf)) != NULL) {
                        goto FoundModule;
                }
                snprintf(pathbuf, sizeof pathbuf, "%s/../lib/ty/%s.ty", chadbuf, name);
                if ((source = slurp(ty, pathbuf)) != NULL) {
                        goto FoundModule;
                }
        }

        snprintf(pathbuf, sizeof pathbuf, "%s.ty", name);

        if ((source = slurp(ty, pathbuf)) == NULL) {
                return NULL;
        }

FoundModule:

        // Probably should never fail since we just read from this file
        if (realpath(pathbuf, chadbuf) == NULL) {
                return NULL;
        }

        if (path_out != NULL) {
                *path_out = S2(chadbuf);
        }

        return source;
}

static char *
slurp_module(Ty *ty, char const *name, char const **path)
{
        char *source = try_slurp_module(ty, name, path);

        if (source == NULL) {
                fail("failed to load module: %s%s%s", TERM(93;1), name, TERM(0));
        }

        return source;
}

static void
add_location(Ty *ty, Expr const *e, usize start_off, usize end_off)
{
        if (
                (e->start.line == -1)
             && (e->start.col  == -1)
        ) {
                return;
        }

        switch (e->type) {
        case EXPRESSION_STATEMENT:
        case STATEMENT_EXPRESSION:
        case STATEMENT_MULTI:
        case STATEMENT_BLOCK:
                return;
        }

        dont_printf(
                "Location: (%zu, %zu) (%d) '%.*s'\n",
                start_off,
                end_off,
                e->type,
                (int)(e->end.s - e->start.s), e->start.s
        );

        avP(
                STATE.expression_locations,
                ((struct eloc) {
                        .start_off = start_off,
                        .end_off = end_off,
                        .e = e
                })
        );
}

static void
add_location_info(Ty *ty)
{
        if (vN(STATE.expression_locations) == 0) {
                return;
        }

        struct eloc *locs = vv(STATE.expression_locations);
        for (int i = 0; i < vN(STATE.expression_locations); ++i) {
                locs[i].p_start = (uptr)(v_(STATE.code, locs[i].start_off));
                locs[i].p_end = (uptr)(v_(STATE.code, locs[i].end_off));
        }

        qsort(
                vv(STATE.expression_locations),
                vN(STATE.expression_locations),
                sizeof (struct eloc),
                eloc_cmp
        );

        xvP(location_lists, STATE.expression_locations);
}

inline static TryState *
get_try(Ty *ty, int i)
{
        if (i < vN(STATE.tries)) {
                return vvL(STATE.tries) - i;
        } else {
                return NULL;
        }
}

inline static int
get_try_ctx(Ty *ty)
{
        TryState *try = get_try(ty, 0);
        return (try != NULL) ? try->ctx : TRY_NONE;
}

inline static TryState *
begin_try(Ty *ty)
{
        return avP(STATE.tries, ((TryState) {
                .t = ++t,
                .ctx = TRY_TRY
        }));
}

inline static TryState *
end_try(Ty *ty)
{
        return vvX(STATE.tries);
}

inline static LoopState *
get_loop(Ty *ty, int i)
{
        if (i < vN(STATE.loops)) {
                return vvL(STATE.loops) - i;
        } else {
                return NULL;
        }
}

inline static void
begin_loop(Ty *ty, bool wr, u32 n)
{
        avP(STATE.loops, ((LoopState) {
                .t = ++t,
                .resources = STATE.resources,
                .wr = wr,
                .n = n
        }));
}

inline static void
end_loop(Ty *ty)
{
        vvX(STATE.loops);
}

inline static int
RequiredParameterCount(Expr const *e)
{
        for (int i = 0; i < vN(e->params); ++i) {
                if (*v_(e->dflts, i) != NULL) {
                        return i;
                }
        }

        return 0;
}

inline static bool
is_call(Expr const *e)
{
        return (e->type == EXPRESSION_METHOD_CALL)
            || (e->type == EXPRESSION_FUNCTION_CALL);
}

inline static bool
is_const(Ty *ty, Scope const *scope, char const *name)
{
        Symbol const *s = scope_lookup(ty, scope, name);
        return s != NULL && SymbolIsConst(s);
}

static bool
any_variadic(Expr * const *args, Expr * const *conds, int n)
{
        for (int i = 0; i < n; ++i) {
                if (
                        (args[i] != NULL)
                     && (args[i]->type == EXPRESSION_SPREAD || conds[i] != NULL)
                ) {
                        return true;
                }
        }

        return false;
}

static bool
is_placeholder(Expr const *e)
{
        return (e == NULL)
            || (e->type == EXPRESSION_PLACEHOLDER);
}

static bool
is_variadic(Expr const *e)
{
        switch (e->type) {
        case EXPRESSION_FUNCTION_CALL:
                return any_variadic(
                        vv(e->args),
                        vv(e->fconds),
                        vN(e->args)
                );
        case EXPRESSION_METHOD_CALL:
        case EXPRESSION_DYN_METHOD_CALL:
                return any_variadic(
                        vv(e->method_args),
                        vv(e->mconds),
                        vN(e->method_args)
                );
        default:
                return false;
        }
}

inline static Scope *
IdentifierScope(Ty *ty, Expr const *expr)
{
        if (
                (expr == NULL)
             || (expr->module == NULL)
             || (*expr->module == '\0')
        ) {
                return SCOPE;
        }

        Scope *scope = search_import_scope(expr->module);

        return (scope != NULL) ? scope : SCOPE;
}

inline static Symbol *
TryResolveIdentifier(Ty *ty, Expr *expr)
{
        u32 flags = 0;
        Scope *scope = IdentifierScope(ty, expr);

        if (expr->module != NULL) {
                flags |= SCOPE_EXPLICIT;
        }

        return ScopeLookupEx(scope, expr->identifier, flags);
}

inline static Symbol *
addsymbolx(Ty *ty, Scope *scope, char const *name, bool check_ns_shadow)
{
        Symbol *s = scope_local_lookup(ty, scope, name);

        if (
                s != NULL
             && SymbolIsConst(s)
             && (scope == STATE.global || scope == GlobalScope)
             && strcmp(name, "_") != 0
        ) {
                fail_or(
                        "redeclaration of variable %s%s%s%s%s",
                        TERM(1),
                        TERM(34),
                        name,
                        TERM(22),
                        TERM(39)
                ) {
                        return s;
                }
        }

        if (
                check_ns_shadow
             && (s = scope_lookup(ty, scope, name)) != NULL
             && SymbolIsNamespace(s)
        ) {
                fail_or(
                        "error: namespace '%s%s%s' shadowed by pattern binding",
                        TERM(93;1),
                        name,
                        TERM(0)
                );
        }

        s = scope_add(ty, scope, name);
        s->mod = STATE.module;
        s->loc = STATE.start;

        if (isupper(name[0])) {
                s->flags |= SYM_PUBLIC;
        }

        return s;
}

inline static Symbol *
addsymbol(Ty *ty, Scope *scope, char const *name)
{
        if (scope->reloading) {
                Symbol *sym = ScopeFindRecycled(scope, name);
                if (sym != NULL) {
                        sym->flags = SYM_GLOBAL;
                        sym->class = -1;
                        sym->tag   = -1;
                        sym->type  = NULL;
                        sym->expr  = NULL;
                        return sym;
                }
        }

        return addsymbolx(ty, scope, name, false);
}

static Symbol *
getsymbol(Ty *ty, Scope const *scope, char const *name, u32 flags)
{
        if (strcmp(name, "_") == 0) {
                fail(
                        "the special identifier %s'_'%s can only be used as an lvalue",
                        TERM(38),
                        TERM(39)
                );
        }

        // Allow -> it + 1 instead of -> _1 + 1
        if (strcmp(name, "it") == 0 && STATE.implicit_fscope != NULL) {
                name = "_1";
        }

        /*
         * let f = -> function () { let _2 = 4; return _1 + _2; };
         *
         * // f = const . (+ 4)
         */
        if (name[0] == '_' && isdigit(name[1]) && name[2] == '\0' && STATE.implicit_fscope != NULL) {
                int n = name[1] - '0';
                for (int i = vN(STATE.implicit_func->params) + 1; i <= n; ++i) {
                        char b[] = { '_', i + '0', '\0' };
                        char *id = sclonea(ty, b);
                        Symbol *sym = addsymbol(ty, STATE.implicit_fscope, id);
                        avP(STATE.implicit_func->params, id);
                        avP(STATE.implicit_func->param_symbols, sym);
                        avP(STATE.implicit_func->dflts, NULL);
                        avP(STATE.implicit_func->constraints, NULL);
                }
        }

        Symbol *s = ScopeLookupEx(scope, name, flags);

        if (s == NULL) {
                fail_or(
                        "reference to undefined variable: %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        name,
                        TERM(0)
                ) {
                        s = &UndefinedSymbol;
                        s->scope = GlobalScope;
                }
        }

        if (
                SymbolIsMember(s)
             && (scope->function != STATE.self->scope)
        ) {
                // Force a capture of `self`
                (void)ScopeLookup(scope->function, "self");
        }

        if (
                SymbolIsMember(s)
             && (STATE.meth->mtype == MT_STATIC)
             && !SymbolIsStatic(s)
        ) {
                fail("instance member '%s' referenced from static context", name);
        }

        if (SymbolIsNamespace(s)) {
                fail("namespace used in illegal context");
        }

        if (
               s->scope->external
            && (s->scope != STATE.module->scope)
            && !SymbolIsPublic(s)
            && !ModuleIsReloading(STATE.module)
        ) {
                fail("reference to non-public external variable '%s'", name);
        }

        return s;
}

inline static Symbol *
ResolveIdentifier(Ty *ty, Expr const *expr)
{
        if (expr->symbol != NULL) {
                return expr->symbol;
        }

        u32    flags = 0;
        Scope *scope = SCOPE;

        if (expr->module != NULL) {
                flags |= SCOPE_EXPLICIT;
                if (*expr->module != '\0') {
                        scope = get_import_scope(ty, expr->module);
                }
        } else {
                scope = SCOPE;
        }

        return getsymbol(ty, scope, expr->identifier, flags);
}

inline static Symbol *
tmpsymbol(Ty *ty, Scope *scope)
{
        Symbol *sym = scope_add(ty, scope, gensym());
        sym->mod = STATE.module;
        sym->loc = STATE.start;
        return sym;
}

static CompileState
freshstate(Ty *ty, Module *mod)
{
        CompileState st = {0};

        st.module = mod;
        st.global = mod->scope;
        st.pscope = scope_new(ty, "(parse)", st.global, false);

        st.class = NULL;
        st.start = st.end = st.mstart = st.mend = Nowhere;

        // == Typechecking ==========
        types_init(ty);
        // ==========================

        avP(st.imports, ((struct import) {
                .mod  = GlobalModule,
                .name = "prelude",
                .pub  = false
        }));

        return st;
}

inline static bool
is_simple_condition(condpart_vector const *parts)
{
        for (int i = 0; i < parts->count; ++i) {
                struct condpart *p = parts->items[i];
                if (p->target != NULL) {
                        return false;
                }
        }

        return true;
}

inline static bool
is_loop(Ty *ty, Stmt const *s)
{
        switch (s->type) {
        case STATEMENT_FOR_LOOP:
        case STATEMENT_EACH_LOOP:
        case STATEMENT_WHILE_MATCH:
        case STATEMENT_WHILE:
                return true;
        default:
                return false;
        }
}

int
Expr2Op(Expr const *e)
{
        int op = -1;

        switch (e->type) {
        case EXPRESSION_PLUS:    op = OP_ADD;     break;
        case EXPRESSION_MINUS:   op = OP_SUB;     break;
        case EXPRESSION_DIV:     op = OP_DIV;     break;
        case EXPRESSION_STAR:    op = OP_MUL;     break;
        case EXPRESSION_PERCENT: op = OP_MOD;     break;
        case EXPRESSION_IN:      op = OP_IN;      break;
        case EXPRESSION_NOT_IN:  op = OP_NOT_IN;  break;
        case EXPRESSION_BIT_OR:  op = OP_BIT_OR;  break;
        case EXPRESSION_BIT_AND: op = OP_BIT_AND; break;
        case EXPRESSION_XOR:     op = OP_BIT_XOR; break;
        case EXPRESSION_SHL:     op = OP_BIT_SHL; break;
        case EXPRESSION_SHR:     op = OP_BIT_SHR; break;
        case EXPRESSION_USER_OP: op = intern(&xD.b_ops, e->op_name)->id;
        }

        return op;
}

static void
resolve_type_choices(Ty *ty, Type *t0, int_vector *cs)
{
        switch (t0->type) {
        case TYPE_CLASS:
        case TYPE_OBJECT:
                avP(*cs, t0->class->i);
                break;

        case TYPE_TUPLE:
                avP(*cs, CLASS_TUPLE);
                break;

        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        resolve_type_choices(ty, v__(t0->types, i), cs);
                }
                break;

        case TYPE_VARIABLE:
        case TYPE_FUNCTION:
        case TYPE_BOTTOM:
                avP(*cs, CLASS_TOP);
                break;

        case TYPE_NIL:
                avP(*cs, CLASS_NIL);
                break;

        default:
                fail("bad operator signature: %s", type_show(ty, t0));
        }
}

static void
resolve_class_choices(Ty *ty, Expr *e, int_vector *cs)
{
        switch (e->type) {
        case EXPRESSION_MATCH_ANY:
                avP(*cs, CLASS_TOP);
                break;

        case EXPRESSION_TYPE:
                resolve_type_choices(ty, e->_type, cs);
                break;

        case EXPRESSION_BIT_OR:
                resolve_class_choices(ty, e->left, cs);
                resolve_class_choices(ty, e->right, cs);
                break;

        case EXPRESSION_TYPE_UNION:
                for (int i = 0; i < vN(e->es); ++i) {
                        resolve_class_choices(ty, v__(e->es, i), cs);
                }
                break;

        default:
                avP(*cs, ResolveClassSpec(ty, e));
        }
}

inline static int
op_signature(Ty *ty, Scope *scope, Expr *e, int_vector *t1, int_vector *t2)
{
        if (vN(e->constraints) > 0 && v__(e->constraints, 0) != NULL) {
                symbolize_expression(ty, scope, v__(e->constraints, 0));
                resolve_class_choices(ty, v__(e->constraints, 0), t1);
        } else {
                avP(*t1, CLASS_TOP);
        }

        if (vN(e->constraints) > 1 && v__(e->constraints, 1) != NULL) {
                symbolize_expression(ty, scope, v__(e->constraints, 1));
                resolve_class_choices(ty, v__(e->constraints, 1), t2);
        } else {
                avP(*t2, CLASS_TOP);
        }

        if (
                (vN(e->params) == 0)
             || (vN(e->params) > 2)
             || (e->ikwargs != -1)
             || (e->rest != -1)
        ) {
                fail("bad operator signature");
        }

        return vN(e->params);
}

static void
symbolize_op_def(Ty *ty, Scope *scope, Stmt *def)
{
        int_vector t1 = {0};
        int_vector t2 = {0};

        Expr *target = def->target;
        Expr   *func = def->value;

        int arity = op_signature(ty, scope, func, &t1, &t2);

        InternSet  *set = (arity == 1) ? &xD.u_ops : &xD.b_ops;
        InternEntry  *e = intern(set, target->identifier);

        target->symbol = scope_add(ty, GlobalScope, target->identifier);
        target->symbol->mod = STATE.module;
        target->symbol->loc = target->start;

        for (int i = 0; i < t1.count; ++i) {
                for (int j = 0; j < t2.count; ++j) {
                        dont_printf(
                                "  %4s :: (%3d) %8s x %-8s (%3d) :: %d\n",
                                e->name,
                                v__(t1, i),
                                class_name(ty, v__(t1, i)),
                                class_name(ty, v__(t2, j)),
                                v__(t2, j),
                                target->symbol->i
                        );
                        if (target->xscope != NULL) {
                                op_add(
                                        e->id,
                                        v__(t1, i),
                                        v__(t2, j),
                                        target->symbol->i,
                                        func
                                );
                        } else {
                                op_add(
                                        e->id,
                                        v__(t1, i),
                                        v__(t2, j),
                                        -1,
                                        func
                                );
                        }
                }
        }
}

int
resolve_name(Ty *ty, Scope const *scope, StringVector const *parts, void **out)
{
        for (int i = 0; i < vN(*parts); ++i) {
                char const *part = v__(*parts, i);
                Symbol *sym = scope_lookup(ty, scope, part);
                if (sym == NULL) {
                        if (
                                i > 0
                             || (scope = search_import_scope(part)) == NULL
                        ) {
                                *out = (void *)part;
                                return TY_NAME_NONE;
                        }
                } else if (!SymbolIsNamespace(sym)) {
                        *out = (void *)sym;
                        return TY_NAME_VARIABLE;
                } else {
                        scope = sym->scope;
                }
        }

        *out = (void *)scope;

        return scope->namespace ? TY_NAME_NAMESPACE
                                : TY_NAME_MODULE;
}

inline static Expr *
resolve_access(Ty *ty, Scope const *scope, char **parts, int n, Expr *e, bool strict)
{
        static byte_vector mod;
        vN(mod) = 0;

        Symbol *sym = NULL;

#if defined(TY_DEBUG_NAMES)
        printf("resolve_access(): parts=[");
        for (int i = 0; i < n; ++i) {
                if (i != 0) printf(", ");
                printf("%s", parts[i]);
        }
        printf("], e=%s\n", ExpressionTypeName(e));
#endif

        if (n == 1) {
                sym = scope_lookup(ty, scope, parts[0]);
                if (sym != NULL && !SymbolIsNamespace(sym)) {
                        return e;
                }
        }

        for (int i = 0; i < n; ++i) {
                dump(&mod, &"/%s"[!i], parts[i]);
        }

        Scope *mod_scope = search_import_scope(vv(mod));
        if (mod_scope != NULL) {
                e->type = EXPRESSION_MODULE;
                e->name = (n == 1) ? parts[0] : sclonea(ty, vv(mod));
                e->scope = mod_scope;
                e->parent = NULL;
                return e;
        }

        if (n == 1) {
                if (sym != NULL) {
                        e->type = EXPRESSION_NAMESPACE;
                        e->name = parts[0];
                        e->scope = sym->scope;
                        e->parent = NULL;
                }
                return e;
        }

        Expr *left;

        switch (e->type) {
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_METHOD_CALL:
                left = e->object;
                break;
        case EXPRESSION_NAMESPACE:
                left = e->parent;
                break;
        default:
                left = NULL;
        }

        if (left == NULL) {
                return e;
        }

        char *id = parts[n - 1];

#if defined(TY_DEBUG_NAMES)
        static int d;
        printf("%*sbefore: left=%s, e=%s, part=%s\n", d*4, "", ExpressionTypeName(left), ExpressionTypeName(e), parts[n - 1]);
        d += 1;
        resolve_access(ty, scope, parts, n - 1, left, strict);
        d -= 1;
        printf("%*safter:  left=%s, e=%s, part=%s\n", d*4, "", ExpressionTypeName(left), ExpressionTypeName(e), id);
#else
        resolve_access(ty, scope, parts, n - 1, left, strict);
#endif

        if (
                (left->type == EXPRESSION_IDENTIFIER)
             || (left->type == EXPRESSION_MEMBER_ACCESS)
        ) {
                return e;
        }

        sym = scope_lookup(ty, left->scope, id);
        if (sym == NULL) {
                if (!strict) return NULL;
                STATE.end = e->end;
                fail_or(
                        "reference to undefined variable: %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        id,
                        TERM(0)
                ) {
                        sym = &UndefinedSymbol;
                }
        } else if (
                !SymbolIsPublic(sym)
             && (
                        left->scope->external
                     || !scope_is_subscope(left->scope, STATE.global)
                )
        ) {
                if (!strict) return NULL;
                STATE.end = e->end;
                fail(
                        "reference to non-public external symbol %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        id,
                        TERM(0)
                );
        }

        if (SymbolIsNamespace(sym)) {
                e->type = EXPRESSION_NAMESPACE;
                e->name = id;
                e->scope = sym->scope;
                e->parent = left;
                return e;
        }

        if (e->type == EXPRESSION_METHOD_CALL) {
                Expr fc = *e;

                fc.type = EXPRESSION_FUNCTION_CALL;
                fc.args = e->method_args;
                fc.kwargs = e->method_kwargs;
                fc.kws = e->method_kws;
                fc.fconds = e->mconds;

                v00(fc.fkwconds);
                for (usize i = 0; i < vN(fc.kws); ++i) {
                        avP(fc.fkwconds, NULL);
                }

                Expr *f = fc.function = NewExpr(ty, EXPRESSION_IDENTIFIER);
                f->start = left->start;
                f->end = e->end;
                f->identifier = id;
                f->namespace = left;
                f->module = NULL;
                f->symbol = sym;
                f->xscope = (Scope *)scope;
                f->xfunc = STATE.func;
                f->_type = sym->type;

                *e = fc;
        } else {
                ZERO_EXPR(e);
                e->type = EXPRESSION_IDENTIFIER;
                e->identifier = id;
                e->namespace = left;
                e->module = "";
                e->symbol = sym;
                e->xscope = (Scope *)scope;
                e->xfunc = STATE.func;
                e->_type = sym->type;
        }

        return e;
}

void
fixup_access(Ty *ty, Scope const *scope, Expr *e, bool strict)
{
        StringVector parts = {0};

        char const *name;
        Location end = e->end;

        if (scope == NULL) {
                scope = STATE.global;
        }

        if (e->type == EXPRESSION_MEMBER_ACCESS) {
                name = e->member->identifier;
                end = e->end;
        } else if (e->type == EXPRESSION_METHOD_CALL) {
                name = e->method->identifier;
                end = e->object->end;
                while (*end.s != '\0' && *end.s != '(') {
                        end.s += 1;
                }
        } else {
                return;
        }

        Expr const *o = e->object;

        while (o != NULL) {
                if (o->type == EXPRESSION_MEMBER_ACCESS) {
                        o = o->object;
                } else if (
                        (o->type == EXPRESSION_NAMESPACE)
                     && (o->parent != NULL)
                ) {
                        o = o->parent;
                } else {
                        break;
                }
        }

        if (o == NULL) {
                return;
        }

        if (
                (o->type != EXPRESSION_MODULE)
             && (o->type != EXPRESSION_NAMESPACE || o->parent != NULL)
             && (o->type != EXPRESSION_IDENTIFIER || o->module != NULL)
        ) {
                return;
        }

        if (o->type == EXPRESSION_IDENTIFIER) {
                Symbol *sym = scope_lookup(ty, scope, o->identifier);
                if (sym != NULL && !SymbolIsNamespace(sym)) {
                        return;
                }
        }

        avP(parts, (char *)name);

        o = e->object;

        for (;;) {
                if (o->type == EXPRESSION_MEMBER_ACCESS) {
                        avI(parts, o->member->identifier, 0);
                        o = o->object;
                } else if (
                        (o->type == EXPRESSION_NAMESPACE)
                     && (o->parent != NULL)
                ) {
                        avI(parts, o->name, 0);
                        o = o->parent;
                } else {
                        break;
                }
        }

        if (o->type == EXPRESSION_IDENTIFIER) {
                avI(parts, o->identifier, 0);
        } else {
                avI(parts, o->name, 0);
        }

#if defined(TY_DEBUG_NAMES)
        printf("parts: ");
        for (int i = 0; i < vN(parts); ++i) {
                if (i > 0) putchar('.');
                printf("%s", v__(parts, i));
        }
        putchar('\n');
#endif

        resolve_access(ty, scope, vv(parts), vN(parts), (Expr *)e, strict);

#if defined(TY_DEBUG_NAMES)
        printf("resolved to: %s\n", ExpressionTypeName(e));
#endif
}

static Scope *
search_import_scope(char const *name)
{
        for (int i = 0; i < vN(STATE.imports); ++i) {
                if (strcmp(name, v_(STATE.imports, i)->name) == 0) {
                        return v_(STATE.imports, i)->mod->scope;
                }
        }

        return NULL;
}

static Scope *
get_import_scope(Ty *ty, char const *name)
{
        Scope *scope = search_import_scope(name);

        if (scope != NULL) {
                return scope;
        }

        if (*name == '\0') {
                return STATE.global;
        }

        if (DEBUGGING) {
                void const *ip = TDB->host->ip;
                Expr const *ctx = (ip != NULL)
                                ? compiler_find_expr(ty, ip)
                                : NULL;

                Module const *this_mod = ExpressionModule(ctx);

                if (this_mod != NULL) {
                        if (strcmp(this_mod->name, name) == 0) {
                                return this_mod->scope;
                        }

                        Module *local_import = GetModuleImport(ty, this_mod, name);

                        if (local_import != NULL) {
                                return local_import->scope;
                        }
                }

                Module const *any_mod = GetModule(ty, name);

                if (any_mod != NULL) {
                        return any_mod->scope;
                }
        }

        if (scope == NULL) {
                fail(
                        "reference to undefined module: %s%s%s%s",
                        TERM(93),
                        TERM(1),
                        name,
                        TERM(0)
                );
        }

        return scope;
}

static void
apply_decorator_macros(Ty *ty, Scope *scope, Expr **ms, int n)
{
        for (int i = 0; i < n; ++i) {
                if (
                        ms[i]->type == EXPRESSION_FUNCTION_CALL &&
                        ms[i]->function->type == EXPRESSION_IDENTIFIER
                ) {
                        symbolize_expression(ty, scope, ms[i]->function);

                        if (!SymbolIsFunMacro(ms[i]->function->symbol)) {
                                fail("non-FLM used as method decorator macro");
                        }

                        invoke_fun_macro(ty, scope, ms[i]);

                        if (ms[i]->type != EXPRESSION_FUNCTION) {
                                fail("method decorator macro returned %s", ExpressionTypeName(ms[i]));
                        }
                }
        }
}

static void
symbolize_methods(Ty *ty, Scope *scope, int class, expression_vector *ms, int mtype)
{
        for (int i = 0; i < vN(*ms); ++i) {
                Expr *meth = v__(*ms, i);
                WITH_STATE(meth, meth) {
                        meth->mtype = mtype;
                        symbolize_expression(ty, scope, meth);
                }
        }
}

static void
symbolize_fields(Ty *ty, Scope *subscope, expression_vector const *fields)
{
        for (int i = 0; i < vN(*fields); ++i) {
                Expr *field = v__(*fields, i);
                switch (field->type) {
                case EXPRESSION_IDENTIFIER:
                        if (field->constraint != NULL) {
                                symbolize_expression(ty, subscope, field->constraint);
                                field->_type = type_fixed(ty, type_resolve(ty, field->constraint));
                                SET_TYPE_SRC(field);
                        }
                        break;
                case EXPRESSION_EQ:
                        if (field->target->type != EXPRESSION_IDENTIFIER) {
                                field = field->target;
                                goto BadField;
                        }
                        symbolize_expression(ty, subscope, field->value);
                        if (field->target->constraint != NULL) {
                                symbolize_expression(ty, subscope, field->target->constraint);
                                field->_type = type_fixed(ty, type_resolve(ty, field->target->constraint));
                                SET_TYPE_SRC(field);
                        }
                        type_assign(ty, field->target, field->value->_type, T_FLAG_STRICT);
                        break;
                default:
                BadField:
                        fail("illegal expression in field definition: %s", ExpressionTypeName(field));
                }
        }
}

static Expr *
mkmulti(Ty *ty, char *name, bool setters)
{
        Expr *multi = NewExpr(ty, EXPRESSION_MULTI_FUNCTION);

        multi->name = name;
        multi->class = -1;

        if (setters) {
                multi->rest = -1;
                multi->ikwargs = -1;
        } else {
                multi->rest = 0;
                multi->ikwargs = 1;
        }

        avP(multi->params, "@");
        avP(multi->params, "%");
        avP(multi->constraints, NULL);
        avP(multi->constraints, NULL);
        avP(multi->dflts, NULL);
        avP(multi->dflts, NULL);

        return multi;
}

static void
aggregate_overloads(
        Ty *ty,
        int class,
        expression_vector *ms,
        add_to_class_fn *add,
        bool setters
)
{
        SCRATCH_SAVE();

        u32 n = vN(*ms);
        qsort(ms->items, n, sizeof *ms->items, method_cmp);

        char *scratch = smA(4096);
        char const *private;

        for (int i = 0; i + 1 < n; ++i) {
                if (
                        (strcmp(ms->items[i]->name, ms->items[i + 1]->name) != 0)
                     || (
                                contains(OperatorCharset, ms->items[i]->name[0])
                        )

                ) {
                        continue;
                }

                char buffer[1024];
                Expr *multi = mkmulti(ty, ms->items[i]->name, setters);
                multi->fn_symbol = ms->items[i]->fn_symbol;

                private = GetPrivateName(multi->name, class, scratch, 4096);
                (*add)(ty, class, private, REF(NewZero()));

                int m = 0;
                do {
                        ms->items[i + m]->fn_symbol = multi->fn_symbol;
                        ms->items[i + m]->overload = multi;
                        snprintf(buffer, sizeof buffer, "%s#%d", ms->items[i + m]->name, m + 1);
                        ms->items[i + m]->name = sclonea(ty, buffer);
                        avP(multi->functions, ms->items[i + m]);
                        m += 1;
                } while (i + m < n && strcmp(ms->items[i + m]->name, multi->name) == 0);

                multi->class = class;

                //RedpillFun(ty, c->def->class.scope, multi, c->object_type);

                avP(*ms, multi);
        }

        qsort(ms->items, vN(*ms), sizeof *ms->items, method_cmp);

        SCRATCH_RESTORE();
}

inline static Symbol *
RegexCapture(Ty *ty, Scope *scope, int i)
{
        char id[16];
        snprintf(id, sizeof id, "$%d", i);

        Symbol *var = addsymbol(ty, scope, sclonea(ty, id));
        var->type = TYPE_STRING;

        return var;
}

static void
add_captures(Ty *ty, Expr *pattern, Scope *scope)
{
        /*
         * /(\w+) = (\d+)/ => $0, $1, $2
         */
        Regex const *re = pattern->regex;
        int n = re->ncap;

        u32 n_named;
        pcre2_pattern_info(re->pcre2, PCRE2_INFO_NAMECOUNT, &n_named);

        char const *names;
        pcre2_pattern_info(re->pcre2, PCRE2_INFO_NAMETABLE, &names);

        pattern->match_symbol = RegexCapture(ty, scope, 0);

        for (int i = 1; i <= n; ++i) {
                char const *nt = names;
                for (int j = 0; j < n_named; ++j) {
                        int capture_index = (nt[0] << 8) + nt[1];
                        nt += 2;

                        if (capture_index == i) {
                                /*
                                 * Don't think clone is necessary here...
                                 */
                                addsymbol(ty, scope, nt)->type = TYPE_STRING;
                                goto NextCapture;
                        }
                }

                /*
                 * This is not a named capture group
                 */
                RegexCapture(ty, scope, i);
        NextCapture:
                ;
        }
}

static bool
try_fun_macro_op(Ty *ty, Scope *scope, Expr *e)
{
        Symbol *sym = scope_lookup(ty, scope, e->op_name);

        if (sym == NULL || !SymbolIsFunMacro(sym)) {
                return false;
        }

        Expr *fun = NewExpr(ty, EXPRESSION_IDENTIFIER);
        fun->xscope = scope;
        fun->xfunc = STATE.func;
        fun->identifier = (char *)e->op_name;
        fun->scope = sym->scope;
        fun->symbol = sym;

        Expr *left = e->left;
        Expr *right =  e->right;

        e->type = EXPRESSION_FUNCTION_CALL;
        e->function = fun;

        v00(e->args);
        v00(e->fconds);

        avP(e->args, left);
        avP(e->fconds, NULL);

        avP(e->args, right);
        avP(e->fconds, NULL);

        invoke_fun_macro(ty, scope, e);

        return true;
}

static void
fix_part(Ty *ty, struct condpart *p, Scope *scope)
{
        if (p->target != NULL) {
                return;
        }

        if (
                p->e->type != EXPRESSION_USER_OP
             || !try_fun_macro_op(ty, scope, p->e)
        ) {
                if (p->e->type != EXPRESSION_FUNCTION_CALL) {
                        return;
                }

                symbolize_expression(ty, scope, p->e->function);

                if (
                        p->e->function->type != EXPRESSION_IDENTIFIER
                     || !SymbolIsFunMacro(p->e->function->symbol)
                ) {
                        return;
                }

                invoke_fun_macro(ty, scope, p->e);
        }

        if (p->e->type == EXPRESSION_EQ) {
                p->target = p->e->target;
                p->e = p->e->value;
                p->def = false;
        } else if (
                (p->e->type == EXPRESSION_STATEMENT)
             && (p->e->statement->type == STATEMENT_DEFINITION)
        ) {
                p->target = p->e->statement->target;
                p->e = p->e->statement->value;
                p->def = true;
        }
}

static void
fixup_choice(Ty *ty, Expr *e, Scope *scope)
{
        if (e == NULL || e->type != EXPRESSION_CHOICE_PATTERN) {
                return;
        }

        expression_vector choices = {0};
        expression_vector to_expand = {0};

        avP(to_expand, e);

        while (vN(to_expand) != 0) {
                Expr *choice = *vvX(to_expand);

                while (expedite_fun(ty, choice, scope)) {
                        continue;
                }

                if (
                        choice != NULL
                     && choice->type == EXPRESSION_CHOICE_PATTERN
                ) {
                        for (int i = 0; i < vN(choice->es); ++i) {
                                avI(to_expand, v__(choice->es, i), 0);
                        }
                } else {
                        avP(choices, choice);
                }
        }

        e->es = choices;
}

void
try_symbolize_application(Ty *ty, Scope *scope, Expr *e)
{
        if (scope == NULL) {
                scope = STATE.pscope;
        }

        bool tag_pattern = e->type == EXPRESSION_TAG_PATTERN_CALL;

        if (e->type == EXPRESSION_FUNCTION_CALL) {
                fixup_access(ty, scope, e->function, false);
        }

        if (e->type == EXPRESSION_METHOD_CALL) {
                fixup_access(ty, scope, e, false);
        }

        if (
                tag_pattern
             || (
                        (e->type == EXPRESSION_FUNCTION_CALL)
                     && (e->function->type == EXPRESSION_IDENTIFIER)
                )
        ) {
                if (!tag_pattern) {
                        symbolize_expression(ty, scope, e->function);
                        if (SymbolIsFunMacro(e->function->symbol)) {
                                invoke_fun_macro(ty, scope, e);
                                try_symbolize_application(ty, scope, e);
                                return;
                        }
                } else {
                        e->type = EXPRESSION_TAG_PATTERN;
                }
                if (tag_pattern || e->function->symbol->tag != -1) {
                        Expr             f = *e;
                        char   *identifier = e->function->identifier;
                        char       *module = e->function->module;
                        Expr    *namespace = e->function->namespace;
                        Expr      **tagged = vv(e->args);
                        int           tagc = vN(e->args);
                        Symbol     *symbol = e->function->symbol;
                        if (!tag_pattern) {
                                e->type = EXPRESSION_TAG_APPLICATION;
                        }
                        e->identifier = identifier;
                        e->module = module;
                        e->symbol = symbol;
                        e->namespace = namespace;
                        e->constraint = NULL;
                        if (tagc == 1 && tagged[0]->type != EXPRESSION_MATCH_REST) {
                                e->tagged = tagged[0];
                        } else {
                                Expr *items = NewExpr(ty, EXPRESSION_TUPLE);
                                items->start = e->start;
                                items->end = e->end;
                                for (int i = 0; i < tagc; ++i) {
                                        avP(items->es, tagged[i]);
                                        avP(items->tconds, NULL);
                                        avP(items->required, true);
                                        avP(items->names, NULL);
                                }
                                for (int i = 0; i < vN(f.kws); ++i) {
                                        avP(items->es, v__(f.kwargs, i));
                                        avP(items->tconds, v__(f.fkwconds, i));
                                        avP(items->required, true);
                                        avP(items->names, v__(f.kws, i));
                                }
                                e->tagged = items;
                        }
                }
        } else if (
                (e->type == EXPRESSION_TAG_APPLICATION)
             && (e->identifier != EmptyString)
             && (e->namespace == NULL)
        ) {
                e->symbol = ResolveIdentifier(ty, e);
        }
}

static void
symbolize_var_decl(Ty *ty, Scope *scope, Expr *target, bool pub)
{
        switch (target->type) {
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_SPREAD:
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_MATCH_ANY:
                break;
        default:
                UNREACHABLE();
        }

        bool is_thread_local = false;

        if (target->type == EXPRESSION_SPREAD) {
                if (target->value->type != EXPRESSION_IDENTIFIER) {
                        fail("spread expression used in lvalue context");
                }
                char *name = target->value->identifier;
                ZERO_EXPR(target);
                target->type = EXPRESSION_MATCH_REST;
                target->identifier = name;
                if (strcmp(target->identifier, "*") == 0) {
                        target->identifier = "_";
                }
        } else if (target->type == EXPRESSION_TAG_PATTERN) {
                symbolize_var_decl(ty, scope, target->tagged, pub);
        }

        if (
                ScopeIsTop(scope)
             && (target->module != NULL)
             && (strcmp(target->module, "__tls") == 0)
        ) {
                is_thread_local = true;
        } else if (target->module != NULL && *target->module != '\0') {
                scope = get_import_scope(ty, target->module);
                pub = true;
        }

        target->symbol = addsymbol(
                ty,
                is_thread_local ? ThreadLocals : scope,
                target->identifier
        );

        target->symbol->flags |= SYM_TRANSIENT;

        if (pub) {
                target->symbol->flags |= SYM_PUBLIC;
        }

        if (is_thread_local) {
                target->symbol = scope_insert(ty, scope, target->symbol);
                target->symbol->flags |= SYM_THREAD_LOCAL;
        }
}

static void
symbolize_decl(Ty *ty, Scope *scope, Expr *target, bool pub)
{
        if (target->mod == NULL) {
                target->mod = STATE.module;
        }

        void *ctx = PushContext(ty, target);

        PushScope(scope);

        STATE.start = target->start;
        STATE.end   = target->end;

        fixup_access(ty, scope, target, true);
        try_symbolize_application(ty, scope, target);

        if (target->xscope != NULL) {
                goto End;
        }

        switch (target->type) {
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_SPREAD:
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_MATCH_ANY:
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_var_decl(ty, scope, target, pub);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_decl(ty, scope, target->tagged, pub);
                break;
        case EXPRESSION_ARRAY:
                for (usize i = 0; i < vN(target->elements); ++i) {
                        symbolize_decl(ty, scope, v__(target->elements, i), pub);
                }
                break;
        case EXPRESSION_DICT:
                for (int i = 0; i < vN(target->keys); ++i) {
                        symbolize_decl(ty, scope, v__(target->values, i), pub);
                }
                break;
        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
                for (int i = 0; i < vN(target->es); ++i) {
                        symbolize_decl(ty, scope, v__(target->es, i), pub);
                }
                break;
        }
End:
        PopScope();
        RestoreContext(ty, ctx);
}

static void
symbolize_lvalue_(Ty *ty, Scope *scope, Expr *target, bool decl, bool pub)
{
        if (target->mod == NULL) {
                target->mod = STATE.module;
        }

        if (target->xscope != NULL) {
                return;
        }

        void *ctx = PushContext(ty, target);

        PushScope(scope);

        STATE.start = target->start;
        STATE.end = target->end;

        fixup_access(ty, scope, target, true);
        try_symbolize_application(ty, scope, target);

        if (target->xscope != NULL) {
                goto End;
        }

        target->xfunc = STATE.func;

        switch (target->type) {
        case EXPRESSION_RESOURCE_BINDING:
                if (
                        (target->symbol == NULL)
                     && (strcmp(target->identifier, "_") == 0)
                ) {
                        target->identifier = gensym();
                }
        case EXPRESSION_SPREAD:
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_MATCH_ANY:
                if (decl) {
                        if (target->symbol == NULL) {
                                symbolize_var_decl(ty, scope, target, pub);
                        }
                        target->symbol->flags &= ~SYM_TRANSIENT;
                        if (target->constraint != NULL) {
                                WITH_CTX(TYPE) {
                                        symbolize_expression(ty, scope, target->constraint);
                                }
                                Type *c0 = ResolveConstraint(ty, target->constraint);
                                if (c0 != NULL) {
                                        c0->src = target;
                                        target->_type = c0;
                                        target->symbol->type = c0;
                                        target->symbol->flags |= SYM_FIXED;
                                }
                        }
                } else {
                        if (target->constraint != NULL) {
                                fail(
                                        "illegal constraint on %s%s%s%s%s in assignment statement",
                                        TERM(1),
                                        TERM(34),
                                        target->identifier,
                                        TERM(39),
                                        TERM(22)
                                );
                        }

                        target->symbol = ResolveIdentifier(ty, target);

                        // Try to patch built-in symbols with definition info when we can
                        if (target->symbol->mod == NULL) {
                                target->symbol->mod = target->mod;
                                target->symbol->loc = target->start;
                        }

                        if (SymbolIsConst(target->symbol)) {
                                fail(
                                        "assignment to const variable %s%s%s%s%s",
                                        TERM(34),
                                        TERM(1),
                                        target->identifier,
                                        TERM(22),
                                        TERM(39)
                                );
                        }
                }
                if (target->type == EXPRESSION_RESOURCE_BINDING) {
                        STATE.resources += 1;
                }
                //===================={ <LSP> }=========================================
                if (
                        FindDefinition && 0
                     && target->start.line == QueryLine
                     && target->start.col  <= QueryCol
                     && target->end.col    >= QueryCol
                     && strcmp(CurrentModulePath(ty), QueryFile) == 0
                ) {
                        QueryResult = target->symbol;
                }
                //===================={ </LSP> }========================================
                break;
        case EXPRESSION_REF_PATTERN:
                symbolize_lvalue_(ty, scope, target->target, false, pub);
                break;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_expression(ty, scope, target->left);
                symbolize_lvalue_(ty, scope, target->right, decl, pub);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_lvalue_(ty, scope, target->tagged, decl, pub);
                if (target->identifier != EmptyString) {
                        target->symbol = ResolveIdentifier(ty, target);
                }
                break;
        case EXPRESSION_ARRAY:
                for (usize i = 0; i < vN(target->elements); ++i) {
                        symbolize_lvalue_(ty, scope, v__(target->elements, i), decl, pub);
                }
                target->atmp = tmpsymbol(ty, scope);
                break;
        case EXPRESSION_DICT:
                if (target->dflt != NULL) {
                        PushContext(ty, target->dflt);
                        fail("unexpected default clause in dict destructuring");
                }
                for (int i = 0; i < vN(target->keys); ++i) {
                        symbolize_expression(ty, scope, v__(target->keys, i));
                        symbolize_lvalue_(ty, scope, v__(target->values, i), decl, pub);
                }
                target->dtmp = tmpsymbol(ty, scope);
                break;
        case EXPRESSION_SUBSCRIPT:
                symbolize_expression(ty, scope, target->container);
                symbolize_expression(ty, scope, target->subscript);
                break;
        case EXPRESSION_DYN_MEMBER_ACCESS:
                symbolize_expression(ty, scope, target->member);
        case EXPRESSION_MEMBER_ACCESS:
                symbolize_expression(ty, scope, target->object);
                break;
        case EXPRESSION_TUPLE:
                target->ltmp = tmpsymbol(ty, scope);
        case EXPRESSION_LIST:
                for (int i = 0; i < vN(target->es); ++i) {
                        symbolize_lvalue_(ty, scope, v__(target->es, i), decl, pub);
                }
                break;
        case EXPRESSION_TEMPLATE_XHOLE:
                WITH_PERMISSIVE_SCOPE {
                        symbolize_lvalue_(ty, scope, target->hole.expr, false, false);
                }
                break;
        default:
                fail("unexpected %s in lvalue context", ExpressionTypeName(target));
        }

        target->xscope = scope;

End:
        PopScope();
        RestoreContext(ty, ctx);
}

static void
symbolize_lvalue(Ty *ty, Scope *scope, Expr *target, bool decl, bool pub)
{
        symbolize_lvalue_(ty, scope, target, decl, pub);

        if (STATE.resources > 0) {
                target->has_resources = true;
                STATE.resources = 0;
        }
}

static void
symbolize_pattern_(Ty *ty, Scope *scope, Expr *e, Scope *reuse, bool def)
{
        if (e == NULL) {
                return;
        }

        if (e->mod == NULL) {
                e->mod = STATE.module;
        }

        if (e->xscope != NULL) {
                return;
        }

        void *ctx = PushContext(ty, e);
        PushScope(scope);

        fixup_access(ty, scope, e, true);
        try_symbolize_application(ty, scope, e);

        STATE.start = e->start;
        STATE.end = e->end;
        e->xfunc = STATE.func;

        Symbol *existing = NULL;

        switch (e->type) {
        case EXPRESSION_RESOURCE_BINDING:
                if (e->symbol == NULL && strcmp(e->identifier, "_") == -1) {
                        e->identifier = gensym();
                }
        case EXPRESSION_IDENTIFIER:
                existing = TryResolveIdentifier(ty, e);
                if (
                        strcmp(e->identifier, "_") != 0
                     && (
                                (existing != NULL && SymbolIsConst(existing))
                             || (existing != NULL && existing->scope == scope && !ScopeIsTop(scope))
                             || (e->module != NULL)
                        )
                ) {
                        e->type = EXPRESSION_MUST_EQUAL;
                        // XXX: fixup_access() left us with an IDENTIFIER which is
                        //      already resolved to a symbol. Ideally we wouldn't
                        //      even need to be aware of that here--we should just
                        //      be able to call getymbol() again below and arrive
                        //      at the same result. But namespaces are kind of a
                        //      hack  right now  so we  need to treat  this as a
                        //      special case.
                        if (e->namespace == NULL) {
                                e->symbol = ResolveIdentifier(ty, e);
                        }
                } else {
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_ALIAS_PATTERN:
        case EXPRESSION_MATCH_ANY:
                        if (existing != NULL && existing->tag != -1) {
                                goto Tag;
                        } else if (reuse != NULL && e->module == NULL) {
                                existing = ScopeLookupLocal(reuse, e->identifier);
                        } else {
                                existing = NULL;
                        }
                        if (e->symbol != NULL) {
                                e->symbol->flags &= ~SYM_TRANSIENT;
                                goto End;
                        }
                        if (existing != NULL) {
                                e->symbol = existing;
                                scope_insert(ty, scope, existing);
                        } else {
                                e->symbol = def ? addsymbolx(ty, scope, e->identifier, true)
                                                : ResolveIdentifier(ty, e);
                                if (reuse != NULL) {
                                        scope_insert(ty, reuse, e->symbol);
                                }
                        }
                        WITH_CTX(TYPE) {
                                symbolize_expression(ty, scope, e->constraint);
                        }
                }
                if (e->type == EXPRESSION_RESOURCE_BINDING) {
                        STATE.resources += 1;
                } else if (e->type == EXPRESSION_TAG_PATTERN) {
                        symbolize_pattern_(ty, scope, e->tagged, reuse, def);
                } else if (e->type == EXPRESSION_ALIAS_PATTERN) {
                        symbolize_pattern_(ty, scope, e->aliased, reuse, def);
                }

                Type *c0 = ResolveConstraint(ty, e->constraint);
                if (c0 != NULL) {
                        unify2(ty, &e->symbol->type, c0);
                        unify2(ty, &e->_type, c0);
                } else if (e->symbol->type == NULL) {
                        Type *t0 = type_var(ty);

                        switch  (e->type) {
                        case EXPRESSION_MATCH_NOT_NIL:
                                e->_type = t0;
                                e->symbol->type = type_not_nil(ty, t0);
                                break;

                        case EXPRESSION_ALIAS_PATTERN:
                                e->_type = e->aliased->_type;
                                e->symbol->type = e->aliased->_type;
                                break;

                        default:
                                e->_type = t0;
                                e->symbol->type = t0;
                                break;
                        }
                }

                //===================={ <LSP> }=========================================
                if (
                        FindDefinition && 0
                     && e->start.line == QueryLine
                     && e->start.col  <= QueryCol
                     && e->end.col    >= QueryCol
                     && strcmp(CurrentModulePath(ty), QueryFile) == 0
                ) {
                        QueryResult = e->symbol;
                }
                //===================={ </LSP> }========================================

                break;
        case EXPRESSION_REF_PATTERN:
                symbolize_lvalue(ty, scope, e->target, false, false);
                e->tmp = tmpsymbol(ty, scope);
                break;
        case EXPRESSION_KW_AND:
                symbolize_pattern_(ty, scope, e->left, reuse, def);
                for (int i = 0; i < vN(e->p_cond); ++i) {
                        struct condpart *p = v__(e->p_cond, i);
                        fix_part(ty, p, scope);
                        symbolize_pattern_(ty, scope, p->target, reuse, p->def);
                        symbolize_expression(ty, scope, p->e);
                }
                e->_type = e->left->_type;
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < vN(e->elements); ++i) {
                        symbolize_pattern_(ty, scope, v__(e->elements, i), reuse, def);
                }
                e->_type = type_array(ty, e);
                break;
        case EXPRESSION_DICT:
                for (int i = 0; i < vN(e->keys); ++i) {
                        symbolize_expression(ty, scope, v__(e->keys, i));
                        symbolize_pattern_(ty, scope, v__(e->values, i), reuse, def);
                }
                break;
        case EXPRESSION_CHOICE_PATTERN:
        {
                fixup_choice(ty, e, scope);

                Scope *shared = scope_new(ty, "(match-shared)", scope, false);

                if (reuse == NULL) {
                        reuse = scope_new(ty, "(match-shared)", scope, false);
                }

                for (int i = 0; i < vN(e->es); ++i) {
                        Scope *subscope = scope_new(ty, "(match-branch)", scope, false);
                        symbolize_pattern_(ty, subscope, v__(e->es, i), reuse, def);
                        scope_copy(ty, shared, subscope);
                }

                scope_copy(ty, scope, shared);

                //if (reuse != NULL) {
                //        scope_copy(ty, reuse, shared);
                //}

                break;
        }
        case EXPRESSION_LIST:
                for (int i = 0; i < vN(e->es); ++i) {
                        symbolize_pattern_(ty, scope, v__(e->es, i), reuse, def);
                }
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < vN(e->es); ++i) {
                        symbolize_pattern_(ty, scope, v__(e->es, i), reuse, def);
                }
                e->_type = type_tuple(ty, e);
                break;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_expression(ty, scope, e->left);
                symbolize_pattern_(ty, scope, e->right, reuse, def);
                break;
        case EXPRESSION_SPREAD:
                if (e->value->type != EXPRESSION_IDENTIFIER) {
                        fail("spread expression used in pattern context");
                }
                e->type = EXPRESSION_MATCH_REST;
                e->identifier = e->value->identifier;
                if (strcmp(e->identifier, "*") == 0) {
                        e->identifier = "_";
                }
                /* fallthrough */
        case EXPRESSION_MATCH_REST:
                e->symbol = addsymbol(ty, scope, e->identifier);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_pattern_(ty, scope, e->tagged, reuse, def);
                e->_type = type_call(ty, e);
                break;
        Tag:
                symbolize_expression(ty, scope, e);
                e->type = EXPRESSION_MUST_EQUAL;
                break;
        case EXPRESSION_CHECK_MATCH:
                symbolize_pattern_(ty, scope, e->left, reuse, def);
                symbolize_expression(ty, scope, e->right);
                e->_type = e->left->_type;
                break;
        case EXPRESSION_REGEX:
                add_captures(ty, e, scope);
                break;
        default:
                symbolize_expression(ty, scope, e);
                break;
        }

End:
        e->xscope = scope;

        PopScope();
        RestoreContext(ty, ctx);
}

static void
symbolize_pattern(Ty *ty, Scope *scope, Expr *e, Scope *reuse, bool def)
{
        symbolize_pattern_(ty, scope, e, reuse, def);

        if (STATE.resources > 0) {
                e->has_resources = true;
                STATE.resources = 0;
        }
}


static bool
expedite_fun(Ty *ty, Expr *e, void *ctx)
{
        if (e->type != EXPRESSION_FUNCTION_CALL)
                return false;

        if (e->function->type != EXPRESSION_IDENTIFIER) {
                return false;
        }

        Symbol *sym = scope_lookup(ty, ctx, e->function->identifier);

        if (sym == NULL) {
                return false;
        }

        symbolize_expression(ty, ctx, e->function);

        if (!SymbolIsFunMacro(e->function->symbol)) {
                return false;
        }

        invoke_fun_macro(ty, ctx, e);

        return true;
}

static void
comptime(Ty *ty, Scope *scope, Expr *e)
{
        symbolize_expression(ty, scope, e->operand);

        Value v = tyeval(ty, e->operand);

        Location mstart = STATE.mstart;
        Location mend = STATE.mend;
        STATE.mstart = STATE.start;
        STATE.mend = STATE.end;

        Expr *ast = cexpr(ty, &v);
        if (ast != NULL) {
                *e = *cexpr(ty, &v);
        } else {
                e->type = EXPRESSION_NIL;
        }

        symbolize_expression(ty, scope, e);

        STATE.mstart = mstart;
        STATE.mend = mend;
}

static void
invoke_fun_macro(Ty *ty, Scope *scope, Expr *e)
{
        add_location_info(ty);
        v00(STATE.expression_locations);

        byte_vector code_save = STATE.code;
        v00(STATE.code);

        ProgramAnnotation annotation = STATE.annotation;
        STATE.annotation = (ProgramAnnotation) {0};

        e->type = EXPRESSION_FUN_MACRO_INVOCATION;

        EE(e->function);
        INSN(HALT);

        v0(STATE.expression_locations);

        vm_exec(ty, vv(STATE.code));

        STATE.code = code_save;
        STATE.annotation = annotation;

        Value m = *vm_get(ty, 0);
        vmX();

        GC_STOP();

        Scope *mscope = STATE.macro_scope;
        STATE.macro_scope = scope;

        void *ctx = PushInfo(
                ty,
                e,
                "invoking function-like macro %s",
                QualifiedName(e->function)
        );

        for (usize i = 0;  i < vN(e->args); ++i) {
                Value v = tyexpr(ty, v__(e->args, i));
                vmP(&v);
        }

        Value v = vmC(&m, vN(e->args));

        Location const mstart = STATE.mstart;
        Location const mend = STATE.mend;

        STATE.mstart = e->start;
        STATE.mend = e->end;

        Expr *origin = STATE.origin;
        CloneContext(ty);
        STATE.origin = ContextList->e;
        *e = *cexpr(ty, &v);
        STATE.origin = origin;

        STATE.mstart = mstart;
        STATE.mend = mend;
        STATE.macro_scope = mscope;

        RestoreContext(ty, ctx);

        GC_RESUME();
}

Scope *
GetNamespace(Ty *ty, Namespace *ns)
{
        if (ns == NULL) {
                return STATE.global;
        }

        Scope *scope = GetNamespace(ty, ns->next);
        Symbol *sym = scope_lookup(ty, scope, ns->id);

        if (sym == NULL) {
                sym = scope_new_namespace(ty, ns->id, scope);
                sym->flags |= SYM_PUBLIC * ns->pub;
#ifdef TY_DEBUG_NAMES
                printf("new ns %s (scope=%s) added to %s\n", ns->id, scope_name(ty, sym->scope), scope_name(ty, scope));
#endif
        } else if (!SymbolIsNamespace(sym)) {
                return STATE.global;
        }

        return sym->scope;
}

static bool
TryResolveExpr(Ty *ty, Scope *scope, Expr *e)
{
        if (e == NULL) {
                return true;
        }

        bool ok = true;

        PushScope(scope);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                e->symbol = TryResolveIdentifier(ty, e);
                ok &= (e->symbol != NULL);
                break;

        case EXPRESSION_COMPILE_TIME:
                ok &= TryResolveExpr(ty, scope, e->operand);
                break;

        case EXPRESSION_SPECIAL_STRING:
                for (int i = 0; i < e->expressions.count; ++i)
                        ok &= TryResolveExpr(ty, scope, e->expressions.items[i]);
                break;

        case EXPRESSION_TAG:
                break;

        case EXPRESSION_TAG_APPLICATION:
                ok &= TryResolveExpr(ty, scope, e->tagged);
                break;

        case EXPRESSION_FUNCTION_TYPE:
                ok &= TryResolveExpr(ty, scope, e->left);
                ok &= TryResolveExpr(ty, scope, e->right);
                break;

        case EXPRESSION_TYPE_OF:
                ok &= TryResolveExpr(ty, scope, e->operand);
                break;

        case EXPRESSION_MATCH:
                ok &= TryResolveExpr(ty, scope, e->subject);
                break;

        case EXPRESSION_USER_OP:
                ok &= TryResolveExpr(ty, scope, e->sc);
        case EXPRESSION_PLUS:
        case EXPRESSION_MINUS:
        case EXPRESSION_STAR:
        case EXPRESSION_DIV:
        case EXPRESSION_PERCENT:
        case EXPRESSION_AND:
        case EXPRESSION_OR:
        case EXPRESSION_WTF:
        case EXPRESSION_CHECK_MATCH:
        case EXPRESSION_LT:
        case EXPRESSION_LEQ:
        case EXPRESSION_GT:
        case EXPRESSION_GEQ:
        case EXPRESSION_CMP:
        case EXPRESSION_DBL_EQ:
        case EXPRESSION_NOT_EQ:
        case EXPRESSION_DOT_DOT:
        case EXPRESSION_DOT_DOT_DOT:
        case EXPRESSION_BIT_OR:
        case EXPRESSION_BIT_AND:
        case EXPRESSION_KW_OR:
        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
                ok &= TryResolveExpr(ty, scope, e->left);
                ok &= TryResolveExpr(ty, scope, e->right);
                break;

        case EXPRESSION_KW_AND:
                // TODO
                break;

        case EXPRESSION_EVAL:
        case EXPRESSION_ENTER:
        case EXPRESSION_PREFIX_HASH:
        case EXPRESSION_PREFIX_BANG:
        case EXPRESSION_PREFIX_QUESTION:
        case EXPRESSION_PREFIX_MINUS:
        case EXPRESSION_PREFIX_AT:
                ok &= TryResolveExpr(ty, scope, e->operand);
                break;

        case EXPRESSION_CONDITIONAL:
                ok &= TryResolveExpr(ty, scope, e->cond);
                ok &= TryResolveExpr(ty, scope, e->then);
                ok &= TryResolveExpr(ty, scope, e->otherwise);
                break;

        case EXPRESSION_STATEMENT:
                // TODO
                break;

        case EXPRESSION_TEMPLATE:
                for (usize i = 0; i < e->template.exprs.count; ++i) {
                        ok &= TryResolveExpr(ty, scope, e->template.exprs.items[i]);
                }
                break;

        case EXPRESSION_FUNCTION_CALL:
                ok &= TryResolveExpr(ty, scope, e->function);
                for (usize i = 0;  i < e->args.count; ++i)

                        ok &= TryResolveExpr(ty, scope, e->args.items[i]);
                for (usize i = 0;  i < e->args.count; ++i)
                        ok &= TryResolveExpr(ty, scope, e->fconds.items[i]);
                for (usize i = 0; i < e->kwargs.count; ++i)
                        ok &= TryResolveExpr(ty, scope, e->kwargs.items[i]);
                break;

        case EXPRESSION_SUBSCRIPT:
                ok &= TryResolveExpr(ty, scope, e->container);
                ok &= TryResolveExpr(ty, scope, e->subscript);
                break;

        case EXPRESSION_SLICE:
                ok &= TryResolveExpr(ty, scope, e->slice.e);
                ok &= TryResolveExpr(ty, scope, e->slice.i);
                ok &= TryResolveExpr(ty, scope, e->slice.j);
                ok &= TryResolveExpr(ty, scope, e->slice.k);
                break;

        case EXPRESSION_MEMBER_ACCESS:
                ok &= TryResolveExpr(ty, scope, e->object);
                break;

        case EXPRESSION_METHOD_CALL:
                ok &= TryResolveExpr(ty, scope, e->object);
                for (usize i = 0;  i < e->method_args.count; ++i)
                        ok &= TryResolveExpr(ty, scope, e->method_args.items[i]);
                for (usize i = 0;  i < e->method_args.count; ++i)
                        ok &= TryResolveExpr(ty, scope, e->mconds.items[i]);
                for (usize i = 0; i < e->method_kwargs.count; ++i)
                        ok &= TryResolveExpr(ty, scope, e->method_kwargs.items[i]);
                break;

        case EXPRESSION_EQ:
        case EXPRESSION_MAYBE_EQ:
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MINUS_EQ:
                ok &= TryResolveExpr(ty, scope, e->value);
                break;

        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_FUNCTION:
                // TODO
                break;

        case EXPRESSION_WITH:
                // TODO
                break;

        case EXPRESSION_THROW:
                ok &= TryResolveExpr(ty, scope, e->throw);
                break;

        case EXPRESSION_YIELD:
                for (int i = 0; i < e->es.count; ++i) {
                    ok &= TryResolveExpr(ty, scope, e->es.items[i]);
                }
                break;

        case EXPRESSION_ARRAY:
                for (usize i = 0; i < e->elements.count; ++i) {
                        ok &= TryResolveExpr(ty, scope, e->elements.items[i]);
                        ok &= TryResolveExpr(ty, scope, e->aconds.items[i]);
                }
                break;

        case EXPRESSION_ARRAY_COMPR:
                ok &= TryResolveExpr(ty, scope, e->compr.iter);
                break;

        case EXPRESSION_DICT:
                ok &= TryResolveExpr(ty, scope, e->dflt);
                for (usize i = 0; i < e->keys.count; ++i) {
                        ok &= TryResolveExpr(ty, scope, e->keys.items[i]);
                        ok &= TryResolveExpr(ty, scope, e->values.items[i]);
                }
                break;

        case EXPRESSION_DICT_COMPR:
                ok &= TryResolveExpr(ty, scope, e->dcompr.iter);
                break;

        case EXPRESSION_LIST:
                for (int i = 0; i < e->es.count; ++i) {
                        ok &= TryResolveExpr(ty, scope, e->es.items[i]);
                }
                break;

        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        ok &= TryResolveExpr(ty, scope, e->es.items[i]);
                        ok &= TryResolveExpr(ty, scope, e->tconds.items[i]);
                }
                break;

        case EXPRESSION_SPREAD:
        case EXPRESSION_SPLAT:
                ok &= TryResolveExpr(ty, scope, e->value);
                break;

        case EXPRESSION_MACRO_INVOCATION:
                break;

        }

        PopScope();

        return ok;
}

static void
symbolize_expression(Ty *ty, Scope *scope, Expr *e)
{
        if (e == NULL || e->xscope != NULL) return;

        if (e->mod == NULL) {
                e->mod = STATE.module;
        }

        if (e->type > EXPRESSION_MAX_TYPE) {
                symbolize_statement(ty, scope, (Stmt *)e);
                return;
        }

        STATE.start = e->start;
        STATE.end = e->end;

        UpdateRefinemenets(ty, scope);

        Symbol *var;
        Scope *subscope;

        Expr             *func = STATE.func;
        Expr    *implicit_func = STATE.implicit_func;
        Scope *implicit_fscope = STATE.implicit_fscope;
        void              *ctx = PushContext(ty, e);

        PushScope(scope);

        fixup_access(ty, scope, e, true);

        if (e->xscope != NULL) {
                goto End;
        }

        e->xfunc = STATE.func;


#if 0
        if (EnableLogging > 0 && e->start.s != NULL) {
                printf(" %4d | %s\n", e->start.line + 1, show_expr(e));
        }
#endif

        Type *t0;
        if (STATE.expected_type != NULL) {
                t0 = STATE.expected_type;
                STATE.expected_type = NULL;
        } else {
                t0 = NULL;
        }

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                LOG("symbolizing var: %s%s%s", (e->module == NULL ? "" : e->module), (e->module == NULL ? "" : "::"), e->identifier);

                if (e->module == NULL && strcmp(e->identifier, "__module__") == 0) {
                        e->type = EXPRESSION_STRING;
                        e->string = CurrentModuleName(ty);
                        break;
                }

                if (e->module == NULL && strcmp(e->identifier, "__file__") == 0) {
                        e->type = EXPRESSION_STRING;
                        e->string = CurrentModulePath(ty);
                        break;
                }

                if (
                        (e->module == NULL)
                     && (strcmp(e->identifier, "__class__") == 0)
                     && (CurrentClassID != -1)
                ) {
                        e->type = EXPRESSION_IDENTIFIER;
                        e->symbol = class_get(ty, CurrentClassID)->def->class.var;
                        break;
                }

                if (e->module == NULL && strcmp(e->identifier, "__func__") == 0) {
                        if (STATE.func && STATE.func->name != NULL) {
                                e->type = EXPRESSION_STRING;
                                e->string = STATE.func->name;
                        } else {
                                e->type = EXPRESSION_NIL;
                        }
                        break;
                }

                if (e->module == NULL && strcmp(e->identifier, "__line__") == 0) {
                        e->type = EXPRESSION_INTEGER;
                        e->integer = STATE.start.line + 1;
                        break;
                }

                if (e->module == NULL && strcmp(e->identifier, "__trace__") == 0) {
                        if (get_try_ctx(ty) != TRY_CATCH) {
                                fail(
                                        "%s%s%s%s%s can only be used inside a catch block",
                                        TERM(1),
                                        TERM(33),
                                        e->identifier,
                                        TERM(39),
                                        TERM(22)
                                );
                        } else {
                                e->type = EXPRESSION_TRACE;
                        }
                        break;
                }

                e->symbol = ResolveIdentifier(ty, e);

                LOG("var %s local", e->local ? "is" : "is NOT");

                if (e->constraint != NULL && false) {
                        fail(
                                "illegal constraint on %s%s%s%s%s in expression context",
                                TERM(1),
                                TERM(34),
                                e->identifier,
                                TERM(39),
                                TERM(22)
                        );
                }

                if (e->symbol->type == NULL) {
                        e->symbol->type = type_var(ty);
                        LOG("ID: %s  ::  %s\n", e->identifier, type_show(ty, e->symbol->type));
                }

                if (
                        SymbolIsProperty(e->symbol)
                     && (TypeType(e->symbol->type) == TYPE_FUNCTION)
                ) {
                        e->_type = e->symbol->type->rt;
                } else {
                        e->_type = e->symbol->type;
                }

                break;
        case EXPRESSION_OPERATOR:
                e->op.u = intern(&xD.members, e->op.id)->id;
                e->op.b = intern(&xD.b_ops, e->op.id)->id;
                e->_type = type_op(ty, e);
                break;
        case EXPRESSION_COMPILE_TIME:
                comptime(ty, scope, e);
                break;
        case EXPRESSION_CAST:
                WITH_CTX(TYPE) {
                        symbolize_expression(ty, scope, e->right);
                }
                WITH_TYPES_OFF {
                        symbolize_expression(ty, scope, e->left);
                }
                e->_type = type_fixed(ty, type_resolve(ty, e->right));
                break;
        case EXPRESSION_SPECIAL_STRING:
                symbolize_expression(ty, scope, e->lang);
                for (int i = 0; i < vN(e->expressions); ++i) {
                        symbolize_expression(ty, scope, v__(e->expressions, i));
                        symbolize_expression(ty, scope, *v_(e->fmts, i));
                        symbolize_expression(ty, scope, *v_(e->fmtfs, i));
                }
                e->_type = type_special_str(ty, e);
                break;
        case EXPRESSION_TAG:
                e->symbol = ResolveIdentifier(ty, e);
                e->_type = e->symbol->type;
                break;
        case EXPRESSION_TAG_APPLICATION:
                if (e->identifier != EmptyString) {
                        e->symbol = ResolveIdentifier(ty, e);
                }
                symbolize_expression(ty, scope, e->tagged);
                e->_type = type_call(ty, e);
                SET_TYPE_SRC(e);
                break;
        case EXPRESSION_MATCH:
                symbolize_expression(ty, scope, e->subject);
                t0 = type_new_inst(ty, e->subject->_type);
                for (int i = 0; i < vN(e->patterns); ++i) {
                        Expr *pat = v__(e->patterns, i);
                        subscope = scope_new(ty, "(match-branch)", scope, false);
                        symbolize_pattern(ty, subscope, pat, NULL, true);
                        ctx = PushContext(ty, pat);
                        unify(ty, &t0, pat->_type);
                        ctx = RestoreContext(ty, ctx);
                        symbolize_expression(ty, subscope, v__(e->thens, i));
                        t0 = type_without(ty, t0, pat->_type);
                }
                e->_type = type_match(ty, e);
                SET_TYPE_SRC(e);
                break;
        case EXPRESSION_UNARY_OP:
                if (try_fun_macro_op(ty, scope, e)) {
                        symbolize_expression(ty, scope, e);
                } else {
                        symbolize_expression(ty, scope, e->operand);
                }
                break;
        case EXPRESSION_USER_OP:
                if (try_fun_macro_op(ty, scope, e)) {
                        symbolize_expression(ty, scope, e);
                        break;
                }
                symbolize_expression(ty, scope, e->sc);
        case EXPRESSION_PLUS:
        case EXPRESSION_MINUS:
        case EXPRESSION_STAR:
        case EXPRESSION_DIV:
        case EXPRESSION_PERCENT:
        case EXPRESSION_XOR:
        case EXPRESSION_SHL:
        case EXPRESSION_SHR:
        case EXPRESSION_CHECK_MATCH:
        case EXPRESSION_CMP:
        case EXPRESSION_BIT_OR:
        case EXPRESSION_BIT_AND:
        case EXPRESSION_KW_OR:
                symbolize_expression(ty, scope, e->left);
                symbolize_expression(ty, scope, e->right);
                e->_type = type_binary_op(ty, e);
                break;
        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
        case EXPRESSION_LT:
        case EXPRESSION_LEQ:
        case EXPRESSION_GT:
        case EXPRESSION_GEQ:
        case EXPRESSION_DBL_EQ:
        case EXPRESSION_NOT_EQ:
                symbolize_expression(ty, scope, e->left);
                symbolize_expression(ty, scope, e->right);
                e->_type = TYPE_BOOL;
                break;
        case EXPRESSION_AND:
                subscope = scope_new(ty, "(&&then)", scope, false);
                symbolize_expression(ty, scope, e->left);
                AddRefinements(ty, e->left, subscope, scope);
                symbolize_expression(ty, subscope, e->right);
                e->_type = type_either(ty, e->left->_type, e->right->_type);
                break;
        case EXPRESSION_OR:
                symbolize_expression(ty, scope, e->left);
                symbolize_expression(ty, scope, e->right);
                e->_type = type_either(ty, e->left->_type, e->right->_type);
                break;
        case EXPRESSION_WTF:
                symbolize_expression(ty, scope, e->left);
                symbolize_expression(ty, scope, e->right);
                e->_type = type_wtf(ty, e);
                break;
        case EXPRESSION_DOT_DOT:
        case EXPRESSION_DOT_DOT_DOT:
                symbolize_expression(ty, scope, e->left);
                symbolize_expression(ty, scope, e->right);
                e->_type = class_get(ty, CLASS_RANGE)->object_type;
                break;
        case EXPRESSION_DEFINED:
                e->type = EXPRESSION_BOOLEAN;
                if (e->module != NULL) {
                        Scope *mscope = search_import_scope(e->module);
                        e->boolean = mscope != NULL && scope_lookup(ty, mscope, e->identifier) != NULL;
                } else {
                        e->boolean = scope_lookup(ty, scope, e->identifier) != NULL;
                }
                e->_type = TYPE_BOOL;
                break;
        case EXPRESSION_IFDEF:
                if (e->module != NULL) {
                        Scope *mscope = search_import_scope(e->module);
                        if (mscope != NULL && scope_lookup(ty, mscope, e->identifier) != NULL) {
                                e->type = EXPRESSION_IDENTIFIER;
                                symbolize_expression(ty, scope, e);
                                e->type = EXPRESSION_IFDEF;
                        } else {
                                e->type = EXPRESSION_NONE;
                        }
                } else {
                        if (scope_lookup(ty, scope, e->identifier) != NULL) {
                                e->type = EXPRESSION_IDENTIFIER;
                                symbolize_expression(ty, scope, e);
                                e->type = EXPRESSION_IFDEF;
                        } else {
                                e->type = EXPRESSION_NONE;
                        }
                }
                break;
        case EXPRESSION_EVAL:
                e->escope = scope;
                scope_capture_all(ty, scope, GlobalScope);
                symbolize_expression(ty, scope, e->operand);
                e->_type = type_var(ty);
                break;
        case EXPRESSION_PREFIX_MINUS:
        case EXPRESSION_PREFIX_QUESTION:
        case EXPRESSION_PREFIX_AT:
        case EXPRESSION_PREFIX_INC:
        case EXPRESSION_PREFIX_DEC:
        case EXPRESSION_POSTFIX_INC:
        case EXPRESSION_POSTFIX_DEC:
                symbolize_expression(ty, scope, e->operand);
                e->_type = e->operand->_type;
                break;
        case EXPRESSION_PREFIX_HASH:
                symbolize_expression(ty, scope, e->operand);
                e->_type = type_unary_hash_t(ty, e->operand->_type);
                break;
        case EXPRESSION_PREFIX_BANG:
                symbolize_expression(ty, scope, e->operand);
                e->_type = TYPE_BOOL;
                break;
        case EXPRESSION_TYPE_OF:
                symbolize_expression(ty, scope, e->operand);
                break;
        case EXPRESSION_ENTER:
                symbolize_expression(ty, scope, e->operand);
                e->_type = type_enter(ty, e->operand->_type);
                break;
        case EXPRESSION_CONDITIONAL:
                subscope = scope_new(ty, "(?:then)", scope, false);
                scope = scope_new(ty, "(?:else)", scope, false);
                symbolize_expression(ty, scope, e->cond);
                AddRefinements(ty, e->cond, subscope, scope);
                symbolize_expression(ty, subscope, e->then);
                symbolize_expression(ty, scope, e->otherwise);
                unify2(ty, &e->_type, e->then->_type);
                unify2(ty, &e->_type, e->otherwise->_type);
                break;
        case EXPRESSION_STATEMENT:
                symbolize_statement(ty, scope, e->statement);
                e->_type = e->statement->_type;
                break;
        case EXPRESSION_TEMPLATE:
                for (usize i = 0; i < vN(e->template.holes); ++i) {
                        symbolize_expression(ty, scope, v__(e->template.holes, i));
                }
                for (usize i = 0; i < vN(e->template.exprs); ++i) {
                        symbolize_expression(ty, scope, v__(e->template.exprs, i));
                }
                var = scope_lookup(ty, GlobalScope, "AST");
                if (var != NULL) {
                        e->_type = var->type;
                }
                break;
        case EXPRESSION_TEMPLATE_XHOLE:
                WITH_PERMISSIVE_SCOPE {
                        symbolize_expression(ty, scope, e->hole.expr);
                }
                break;
        case EXPRESSION_FUNCTION_CALL:
                symbolize_expression(ty, scope, e->function);

                if (
                        (e->function->type == EXPRESSION_IDENTIFIER)
                     && SymbolIsFunMacro(e->function->symbol)
                ) {
                        invoke_fun_macro(ty, scope, e);
                        symbolize_expression(ty, scope, e);
                        break;
                }

                if (e->function->type == EXPRESSION_SELF_ACCESS) {
                        Expr call = *e;
                        call.type = EXPRESSION_METHOD_CALL;
                        call.object = e->function->object;
                        call.method = e->function->member;
                        call.method_args = e->args;
                        call.method_kws = e->kws;
                        call.method_kwargs = e->kwargs;
                        call.mconds = e->fconds;
                        call.maybe = false;
                        *e = call;
                        symbolize_expression(ty, scope, e);
                        break;
                }

                t0 = e->function->_type;

                for (usize i = 0;  i < vN(e->args); ++i) {
                        Type *arg0 = NULL;
                        if (
                                (TypeType(e->function->_type) == TYPE_FUNCTION)
                             && (vN(t0->params) > i)
                        ) {
                                if (vN(t0->bound) > 0) {
                                        t0 = type_inst(ty, t0);
                                }
                                arg0 = v_(t0->params, i)->type;
                        }
                        WITH_EXPECTED_TYPE(arg0) {
                                symbolize_expression(ty, scope, v__(e->args, i));
                        }
                }

                for (usize i = 0;  i < vN(e->args); ++i) {
                        symbolize_expression(ty, scope, v__(e->fconds, i));
                }

                for (usize i = 0; i < vN(e->kwargs); ++i) {
                        symbolize_expression(ty, scope, v__(e->kwargs, i));
                }

                for (usize i = 0; i < vN(e->fkwconds); ++i) {
                        symbolize_expression(ty, scope, v__(e->fkwconds, i));
                }

                e->_type = type_call(ty, e);
                SET_TYPE_SRC(e);

                break;
        case EXPRESSION_SUBSCRIPT:
                symbolize_expression(ty, scope, e->container);
                symbolize_expression(ty, scope, e->subscript);
                if (IS_CTX(EXPR)) {
                        e->_type = type_subscript(ty, e);
                        SET_TYPE_SRC(e);
                }
                break;
        case EXPRESSION_SLICE:
                symbolize_expression(ty, scope, e->slice.e);
                symbolize_expression(ty, scope, e->slice.i);
                symbolize_expression(ty, scope, e->slice.j);
                symbolize_expression(ty, scope, e->slice.k);
                e->_type = type_slice(ty, e);
                SET_TYPE_SRC(e);
                break;
        case EXPRESSION_DYN_MEMBER_ACCESS:
                symbolize_expression(ty, scope, e->member);
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                symbolize_expression(ty, scope, e->object);
                e->_type = type_member_access(ty, e);
                SET_TYPE_SRC(e);
                //===================={ <LSP> }=========================================
                if (FindDefinition && 0 && e->type == EXPRESSION_METHOD_CALL) {
                        ProposeMemberDefinition(ty, e->start, e->end, e->object, e->member->identifier);
                }
                //===================={ </LSP> }========================================
                break;
        case EXPRESSION_DYN_METHOD_CALL:
                symbolize_expression(ty, scope, e->method);
        case EXPRESSION_METHOD_CALL:
                symbolize_expression(ty, scope, e->object);
                t0 = type_member_access_t(
                        ty,
                        e->object->_type,
                        e->method->identifier,
                        false
                );
                for (usize i = 0;  i < vN(e->method_args); ++i) {
                        Type *arg0 = NULL;

                        if ((TypeType(t0) == TYPE_FUNCTION) && (vN(t0->params) > i)) {
                                if (vN(t0->bound) > 0) {
                                        t0 = type_inst(ty, t0);
                                }
                                arg0 = v_(t0->params, i)->type;
                        }

                        WITH_EXPECTED_TYPE(arg0) {
                                symbolize_expression(ty, scope, v__(e->method_args, i));
                        }
                }
                for (usize i = 0;  i < vN(e->method_args); ++i) {
                        symbolize_expression(ty, scope, v__(e->method_args, i));
                }
                for (usize i = 0;  i < vN(e->method_args); ++i) {
                        symbolize_expression(ty, scope, v__(e->mconds, i));
                }
                for (usize i = 0; i < vN(e->method_kwargs); ++i) {
                        symbolize_expression(ty, scope, v__(e->method_kwargs, i));
                }
                e->_type = type_method_call(ty, e);
                SET_TYPE_SRC(e);
                //===================={ <LSP> }=========================================
                if (FindDefinition && 0 && e->type == EXPRESSION_METHOD_CALL) {
                        ProposeMemberDefinition(ty, e->method->start, e->method->end, e->object, e->method->identifier);
                }
                //===================={ </LSP> }========================================
                break;
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MOD_EQ:
        case EXPRESSION_MINUS_EQ:
        case EXPRESSION_AND_EQ:
        case EXPRESSION_OR_EQ:
        case EXPRESSION_XOR_EQ:
        case EXPRESSION_SHL_EQ:
        case EXPRESSION_SHR_EQ:
                symbolize_expression(ty, scope, e->value);
                symbolize_lvalue(ty, scope, e->target, false, false);
                e->_type = e->target->_type;
                break;
        case EXPRESSION_MAYBE_EQ:
        case EXPRESSION_EQ:
                symbolize_expression(ty, scope, e->value);
                symbolize_lvalue(ty, scope, e->target, false, false);
                type_assign(
                        ty,
                        e->target,
                        e->value->_type,
                        T_FLAG_STRICT | T_FLAG_UPDATE
                );
                e->_type = e->value->_type;
                break;
        case EXPRESSION_FUNCTION_TYPE:
                if (e->left->type == EXPRESSION_TUPLE) {
                        for (int i = 0; i < vN(e->left->es); ++i) {
                        }
                }
                symbolize_expression(ty, scope, e->left);
                symbolize_expression(ty, scope, e->right);
                break;
        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_FUNCTION:
        {
                TryStates tries = STATE.tries;
                v00(STATE.tries);

                STATE.func = e;

                // TODO
                bool required = true;

#if defined(TY_PROFILE_TYPES)
                u64 time_start = TyThreadCPUTime();
                u64 allocs_start = TypeAllocCounter;
#endif

                if (e->scope == NULL) {
                        RedpillFun(ty, scope, e, NULL);
                }

                if (
                        (e->type != EXPRESSION_MULTI_FUNCTION)
                     && (e->type != EXPRESSION_IMPLICIT_FUNCTION)
                ) {
                        e->_type = type_function(ty, e, false);
                        SET_TYPE_SRC(e);
                }

                type_scope_push(ty, e);

                if (e->fn_symbol != NULL) {
                        e->fn_symbol->type = e->_type;
                        e->fn_symbol->expr = e;
                }

                if (e->class < 0) {
                        LOG(
                                "================================================== %s[%s:%d]() === %s",
                                (e->name != NULL) ? e->name : "(anon)",
                                CurrentModuleName(ty),
                                e->start.line + 1,
                                type_show(ty, e->_type)
                        );
                } else {
                        LOG(
                                "================================================ %s.%s() === %s\n",
                                class_name(ty, e->class),
                                e->name,
                                type_show(ty, e->_type)
                        );
                }

                if (
                        (e->type == EXPRESSION_FUNCTION)
                     && (
                                (TypeType(t0) == TYPE_FUNCTION)
                             || (TypeType(t0) == TYPE_ALIAS)
                        )
                ) {
                        unify(ty, &e->_type, t0);
                }

                if (e->type == EXPRESSION_IMPLICIT_FUNCTION) {
                        STATE.implicit_fscope = e->scope;
                        STATE.implicit_func = e;

                        WITH_SELF(e->self) {
                                symbolize_statement(ty, e->scope, e->body);
                        }

                        e->type = EXPRESSION_FUNCTION;

                        STATE.implicit_fscope = implicit_fscope;
                        STATE.implicit_func = implicit_func;

                        e->_type = type_function(ty, e, false);
                        SET_TYPE_SRC(e);

                } else {
                        WITH_SELF(e->self) {
                                symbolize_statement(ty, e->scope, e->body);
                        }
                }

                if (
                       (e->_type != NULL)
                    && (e->body != NULL)
                    && !e->body->will_return
                    && (e->type != EXPRESSION_GENERATOR)
                ) {
                        unify(
                                ty,
                                &e->_type->rt,
                                (e->body->_type == NULL) ? NIL_TYPE : e->body->_type
                        );
                }

                e->bound_symbols.items = e->scope->owned.items;
                vN(e->bound_symbols) = vN(e->scope->owned);

                STATE.func = func;
                STATE.tries = tries;

                if (e->type == EXPRESSION_MULTI_FUNCTION) {
                        e->_type = NULL;
                        for (int i = 0; i < vN(e->functions); ++i) {
                                Expr const *fun = v__(e->functions, i);
                                Type *f0 = (fun->type == STATEMENT_FUNCTION_DEFINITION)
                                         ? ((Stmt *)fun)->value->_type
                                         : fun->_type;
                                e->_type = type_both(ty, e->_type, f0);
                        }
                }

                if (CurrentClassID == -1) {
                        LOG("=== %s() === %s\n", e->name, type_show(ty, e->_type));
                } else {
                        LOG("=== %s.%s() === %s\n", class_name(ty, CurrentClassID), e->name, type_show(ty, e->_type));
                }

                type_scope_pop(ty);
                type_function_fixup(ty, e);

                if (e->fn_symbol != NULL) {
                        e->fn_symbol->type = e->_type;
                }

                if (e->type == EXPRESSION_GENERATOR) {
                        e->_type = type_generator(ty, e);
                }

                for (int i = 0; i < vN(e->decorators); ++i) {
                        Expr *dec = v__(e->decorators, i);
                        symbolize_expression(ty, scope, dec);
                        switch (dec->type) {
                        case EXPRESSION_FUNCTION_CALL:
                                v__(dec->args, 0)->_type = e->_type;
                                break;

                        case EXPRESSION_METHOD_CALL:
                                v__(dec->method_args, 0)->_type = e->_type;
                                break;

                        default:
                                UNREACHABLE();
                        }
                }

#if defined(TY_PROFILE_TYPES)
                if (STATE.func == NULL) {
                        u64 time_end = TyThreadCPUTime();
                        u64 allocs_end = TypeAllocCounter;

                        u64 elapsed = time_end - time_start;
                        u64 allocated = allocs_end - allocs_start;

                        if (e->class != -1) {
                                printf(
                                        "%"PRIu64" %"PRIu64" %s::%s.%s\n",
                                        elapsed,
                                        allocated,
                                        CurrentModuleName(ty),
                                        class_name(ty, e->class),
                                        e->name
                                );
                        } else {
                                printf(
                                        "%"PRIu64" %"PRIu64" %s::%s\n",
                                        elapsed,
                                        allocated,
                                        CurrentModuleName(ty),
                                        e->name
                                );
                        }
                }
#endif

                break;
        }
        case EXPRESSION_WITH:
                subscope = scope_new(ty, "(with)", scope, false);
                symbolize_statement(ty, subscope, e->with.block);
                for (int i = 0; i < subscope->size; ++i) {
                        for (Symbol *sym = subscope->table[i]; sym != NULL; sym = sym->next) {
                                // Make sure it's not a tmpsymbol() symbol
                                if (!isdigit(sym->identifier[0])) {
                                        avP(vvL(e->with.block->statements)[0]->try.finally->drop, sym);
                                }
                        }
                }
                e->_type = e->with.block->_type;
                break;
        case EXPRESSION_THROW:
                symbolize_expression(ty, scope, e->throw);
                break;
        case EXPRESSION_YIELD:
                for (int i = 0; i < vN(e->es); ++i) {
                        symbolize_expression(ty, scope, v__(e->es, i));
                }
                if (STATE.func->_type != NULL) {
                        unify2(
                                ty,
                                &STATE.func->_type->rt,
                                type_tagged(ty, TAG_SOME, v__(e->es, 0)->_type)
                        );
                }
                break;
        case EXPRESSION_ARRAY:
                if (IS_CTX(TYPE) && vN(e->elements) == 1) {
                        Expr *elem0 = v__(e->elements, 0);
                        e->type = EXPRESSION_SUBSCRIPT;
                        e->container = NewExpr(ty, EXPRESSION_IDENTIFIER);
                        e->container->identifier = "Array";
                        e->container->symbol = class_get(ty, CLASS_ARRAY)->def->class.var;
                        e->subscript = elem0;
                        symbolize_expression(ty, scope, e);
                        break;
                }
                for (usize i = 0; i < vN(e->elements); ++i) {
                        if (v__(e->aconds, i) != NULL) {
                                subscope = scope_new(ty, "(array-cond)", scope, false);
                                symbolize_expression(ty, subscope, v__(e->aconds, i));
                                AddRefinements(ty, v__(e->aconds, i), subscope, NULL);
                                symbolize_expression(ty, subscope, v__(e->elements, i));
                        } else {
                                symbolize_expression(ty, scope, v__(e->elements, i));
                        }
                }
                e->_type = type_array(ty, e);
                SET_TYPE_SRC(e);
                break;
        case EXPRESSION_ARRAY_COMPR:
                symbolize_expression(ty, scope, e->compr.iter);
                subscope = scope_new(ty, "(array compr)", scope, false);
                symbolize_lvalue(ty, subscope, e->compr.pattern, true, false);
                type_assign_iterable(ty, e->compr.pattern, e->compr.iter->_type, 0);
                symbolize_statement(ty, subscope, e->compr.where);
                symbolize_expression(ty, subscope, e->compr.cond);
                for (usize i = 0; i < vN(e->elements); ++i) {
                        symbolize_expression(ty, subscope, v__(e->elements, i));
                        symbolize_expression(ty, subscope, v__(e->aconds, i));
                }
                e->_type = type_array(ty, e);
                SET_TYPE_SRC(e);
                break;
        case EXPRESSION_DICT:
                symbolize_expression(ty, scope, e->dflt);
                for (usize i = 0; i < vN(e->keys); ++i) {
                        symbolize_expression(ty, scope, v__(e->keys, i));
                        symbolize_expression(ty, scope, v__(e->values, i));
                }
                e->_type = type_dict(ty, e);
                SET_TYPE_SRC(e);
                break;
        case EXPRESSION_DICT_COMPR:
                symbolize_expression(ty, scope, e->dcompr.iter);
                subscope = scope_new(ty, "(dict compr)", scope, false);
                symbolize_lvalue(ty, subscope, e->dcompr.pattern, true, false);
                type_assign_iterable(ty, e->dcompr.pattern, e->dcompr.iter->_type, 0);
                symbolize_statement(ty, subscope, e->dcompr.where);
                symbolize_expression(ty, subscope, e->dcompr.cond);
                for (usize i = 0; i < vN(e->keys); ++i) {
                        symbolize_expression(ty, subscope, v__(e->keys, i));
                        symbolize_expression(ty, subscope, v__(e->values, i));
                }
                e->_type = type_dict(ty, e);
                break;
        case EXPRESSION_TYPE_UNION:
                for (int i = 0; i < vN(e->es); ++i) {
                        symbolize_expression(ty, scope, v__(e->es, i));
                }
                SET_TYPE_SRC(e);
                break;
        case EXPRESSION_LIST:
                for (int i = 0; i < vN(e->es); ++i) {
                        symbolize_expression(ty, scope, v__(e->es, i));
                }
                e->_type = type_list(ty, e);
                SET_TYPE_SRC(e);
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < vN(e->es); ++i) {
                        symbolize_expression(ty, scope, v__(e->es, i));
                        symbolize_expression(ty, scope, v__(e->tconds, i));
                }
                e->_type = type_tuple(ty, e);
                SET_TYPE_SRC(e);
                if (IS_CTX(TYPE) && has_any_names(e)) {
                        e->type = EXPRESSION_TUPLE_SPEC;
                }
                break;
        case EXPRESSION_SPREAD:
                symbolize_expression(ty, scope, e->value);
                e->_type = e->value->_type;
                break;
        case EXPRESSION_SPLAT:
                symbolize_expression(ty, scope, e->value);
                e->_type = e->value->_type;
                break;
        case EXPRESSION_SUPER:
                if (CurrentClassID == -1) {
                        fail("%ssuper%s referenced outside of class context", TERM(95;1), TERM(0));
                }
                if (STATE.meth->mtype != MT_STATIC) {
                        e->symbol = STATE.self;
                }
                break;
        case EXPRESSION_INTEGER:
                e->_type = type_integer(ty, e->integer);
                break;
        case EXPRESSION_REAL:
                e->_type = TYPE_FLOAT;
                break;
        case EXPRESSION_BOOLEAN:
                e->_type = TYPE_BOOL;
                break;
        case EXPRESSION_STRING:
                e->_type = TYPE_STRING;
                break;
        case EXPRESSION_REGEX:
                e->_type = e->regex->detailed ? TYPE_REGEXV : TYPE_REGEX;
                break;
        case EXPRESSION_NIL:
                e->_type = NIL_TYPE;
                break;
        case EXPRESSION_MATCH_REST:
                fail("*<identifier> 'match-rest' pattern used outside of pattern context");
        }

        if (e->_type == NULL) {
                e->_type = type_var(ty);
                SET_TYPE_SRC(e);
        }

        e->xscope = scope;
End:
        RestoreContext(ty, ctx);
        PopScope();

        dont_printf(">>> %s\n", ExpressionTypeName(e));
        dont_printf("::) %s\n", type_show(ty, e->_type));
}

static char *
StyledNameParts(Ty *ty, StringVector const *names)
{
        byte_vector buf = {0};

        for (u32 i = 0; i < vN(*names); ++i) {
                if (i > 0) {
                        sxdf(&buf, "%s%s%s", TERM(38:2:156:148:134), ".", TERM(0));
                }
                sxdf(&buf, "%s%s%s", TERM(93), v__(*names, i), TERM(0));
        }

        return vv(buf);
}

void
CompilerDoUse(Ty *ty, Stmt *s, Scope *scope)
{
        void       *use;
        Scope      *other;
        char const *conflict;

        if (scope == NULL) {
                scope = STATE.pscope;
        }

        void *ctx = PushContext(ty, s);

        switch (
                resolve_name(
                        ty,
                        scope,
                        &s->use.name,
                        &use
                )
        ) {
        case TY_NAME_VARIABLE:
                if (vN(s->use.names) == 0) {
                        scope_insert(ty, scope, use);
                } else {
                        fail(
                                "%suse%s statement includes an import list but "
                                "%s%s%s resolved to a variable",
                                TERM(95;1),
                                TERM(0),
                                TERM(93),
                                StyledNameParts(ty, &s->use.name),
                                TERM(0)
                        );

                }
                break;

        case TY_NAME_MODULE:
        case TY_NAME_NAMESPACE:
                other = use;
                if (vN(s->use.names) == 0) {
                        conflict = scope_copy_public(ty, scope, other, false);
                        if (conflict != NULL) {
                                fail(
                                        "%suse%s imports conflicting symbol %s%s%s",
                                        TERM(95;1),
                                        TERM(0),
                                        TERM(93),
                                        conflict,
                                        TERM(0)
                                );
                        }
                } else {
                        for (u32 i = 0; i < vN(s->use.names); ++i) {
                                Symbol *sym = scope_lookup(ty, other, v__(s->use.names, i));
                                if (sym == NULL) {
                                        fail(
                                                "%suse%s subject %s%s%s does not export %s%s%s",
                                                TERM(95;1),
                                                TERM(0),
                                                TERM(93),
                                                StyledNameParts(ty, &s->use.name),
                                                TERM(0),
                                                TERM(93),
                                                v__(s->use.names, i),
                                                TERM(0)
                                        );
                                } else if (sym->mod != STATE.module && !SymbolIsPublic(sym)) {
                                        fail(
                                                "%suse%s statement attempts to import private symbol %s%s%s.%s%s%s",
                                                TERM(95;1),
                                                TERM(0),
                                                TERM(93),
                                                StyledNameParts(ty, &s->use.name),
                                                TERM(0),
                                                TERM(93),
                                                v__(s->use.names, i),
                                                TERM(0)
                                        );
                                } else {
                                        scope_insert(ty, scope, sym);
                                }
                        }
                }
                break;

        case TY_NAME_NONE:
                fail(
                        "%suse%s statement references undefined name %s%s%s",
                        TERM(95;1),
                        TERM(0),
                        TERM(93),
                        use,
                        TERM(0)
                );

        default:
                UNREACHABLE("resolve_name(): unrecognized return value");
        }

        RestoreContext(ty, ctx);
}

static Scope *
DisableRefinements(Ty *ty, Scope *scope)
{
        if (NO_TYPES) {
                return scope;
        }

        while (scope != NULL && !scope->active) {
                for (int i = 0; i < vN(scope->refinements); ++i) {
                        Refinement *ref = v_(scope->refinements, i);
                        if (ref->active) {
                                if (EnableLogging) {
                                        dont_printf("Disable(%s):\n", ref->var->identifier);
                                        dont_printf("    %s\n", type_show(ty, ref->var->type));
                                        dont_printf("--> %s\n", type_show(ty, ref->t0));
                                }
                                SWAP(Type *, ref->t0, ref->var->type);
                                ref->active = false;
                                if (ref->mut) {
                                        unify2(ty, &ref->var->type, ref->t0);
                                }
                        }
                }
                scope = scope->parent;
        }

        return scope;
}

static void
EnableRefinements(Ty *ty, Scope *scope, Scope *stop)
{
        if (NO_TYPES) {
                return;
        }

        while (scope != stop) {
                for (int i = 0; i < vN(scope->refinements); ++i) {
                        Refinement *ref = v_(scope->refinements, i);
                        if (!ref->active) {
                                if (EnableLogging) {
                                        dont_printf("Enable(%s):\n", ref->var->identifier);
                                        dont_printf("    %s\n", type_show(ty, ref->var->type));
                                        dont_printf("--> %s\n", type_show(ty, ref->t0));
                                }
                                SWAP(Type *, ref->t0, ref->var->type);
                                ref->active = true;
                        }
                }
                scope = scope->parent;
        }
}

inline static void
SetActive(Scope *scope)
{
        if (NO_TYPES) {
                return;
        }

        while (scope != NULL) {
                scope->active = true;
                scope = scope->parent;
        }
}

inline static void
ClearActive(Scope *scope)
{
        if (NO_TYPES) {
                return;
        }

        while (scope != NULL) {
                scope->active = false;
                scope = scope->parent;
        }
}

static void
AddRefinements(Ty *ty, Expr const *e, Scope *_then, Scope *_else)
{
        if (NO_TYPES || e == NULL) {
                return;
        }

        switch (e->type) {
        case EXPRESSION_AND:
                AddRefinements(ty, e->left, _then, _else);
                AddRefinements(ty, e->right, _then, _else);
                break;

        case EXPRESSION_PREFIX_BANG:
                AddRefinements(ty, e->operand, _else, _then);
                break;

        case EXPRESSION_DBL_EQ:
                if (
                        e->left->type == EXPRESSION_IDENTIFIER
                     && e->right->type == EXPRESSION_NIL
                ) {
                        if (_then != NULL) {
                                ScopeRefineVar(
                                        ty,
                                        _then,
                                        e->left->symbol,
                                        NIL_TYPE
                                );
                        }
                        if (_else != NULL) {
                                ScopeRefineVar(
                                        ty,
                                        _else,
                                        e->left->symbol,
                                        type_not_nil(ty, e->left->symbol->type)
                                );
                        }
                }
                break;

        case EXPRESSION_NOT_EQ:
                if (
                        e->left->type == EXPRESSION_IDENTIFIER
                     && e->right->type == EXPRESSION_NIL
                ) {
                        e = e->left;
                        if (_else != NULL) {
                                ScopeRefineVar(
                                        ty,
                                        _else,
                                        e->symbol,
                                        NIL_TYPE
                                );
                        }
                } else {
                        break;
                }
                //fall

        case EXPRESSION_IDENTIFIER:
                if (_then != NULL) {
                        ScopeRefineVar(
                                ty,
                                _then,
                                e->symbol,
                                type_not_nil(ty, e->symbol->type)
                        );
                        Refinement *ref = vvL(_then->refinements);
                        dont_printf("AddRefinement(%s):\n", ref->var->identifier);
                        dont_printf("    %s\n", type_show(ty, ref->var->type));
                        dont_printf("--> %s\n", type_show(ty, ref->t0));
                }
                break;

        case EXPRESSION_CHECK_MATCH:
                if (
                        (e->left->type == EXPRESSION_IDENTIFIER)
                     && IsClassName(e->right)
                ) {
                        dont_printf("=== NewRefinement(%s): %s\n", p->e->left->identifier, type_show(ty, p->e->left->symbol->type));
                        if (_then != NULL) {
                                ScopeRefineVar(
                                        ty,
                                        _then,
                                        e->left->symbol,
                                        type_instance_of(
                                                ty,
                                                e->left->symbol->type,
                                                e->right->symbol->class
                                        )
                                );
                        }
                        if (_else != NULL) {
                                ScopeRefineVar(
                                        ty,
                                        _else,
                                        e->left->symbol,
                                        type_without(
                                                ty,
                                                e->left->symbol->type,
                                                class_get(ty, e->right->symbol->class)->object_type
                                        )
                                );
                        }
                        Refinement *ref = vvL(_then->refinements);
                        dont_printf("AddRefinement(%s):\n", ref->var->identifier);
                        dont_printf("    %s\n", type_show(ty, ref->var->type));
                        dont_printf("--> %s\n", type_show(ty, ref->t0));
                }
                break;
        }
}

static void
UpdateRefinemenets(Ty *ty, Scope *scope)
{
        if (scope != STATE.active) {
                ClearActive(STATE.active);
                SetActive(scope);
                Scope *stop = DisableRefinements(ty, STATE.active);
                EnableRefinements(ty, scope, stop);
                STATE.active = scope;
        } else {
                EnableRefinements(ty, scope, scope->parent);
        }
}

static void
symbolize_statement(Ty *ty, Scope *scope, Stmt *s)
{
        Scope           *subscope;
        Scope           *subscope2;
        ClassDefinition       *cd;

        if (s == NULL || s->xscope != NULL) {
                return;
        }

        if (s->mod != NULL && s->start.s != NULL) {
                dont_printf("%18s:%4d  |  %s\n", s->mod->path, s->start.line + 1, show_expr((Expr *)s));
        }

        STATE.start = s->start;
        STATE.end   = s->end;
        s->xfunc    = STATE.func;
        s->mod      = STATE.module;

        if (scope == STATE.global && s->ns != NULL) {
                scope = GetNamespace(ty, s->ns);
        }

        UpdateRefinemenets(ty, scope);

        void *ctx = PushContext(ty, s);

        PushScope(scope);

        switch (s->type) {
        case STATEMENT_IMPORT:
                import_module(ty, s);
                break;
        case STATEMENT_USE:
                CompilerDoUse(ty, s, scope);
                break;
        case STATEMENT_DEFER:
                if (STATE.func == NULL) {
                        fail("invalid defer statement (not inside of a function)");
                }
                STATE.func->has_defer = true;
        case STATEMENT_EXPRESSION:
                symbolize_expression(ty, scope, s->expression);
                s->_type = s->expression->_type;
                s->will_return = WillReturn(s->expression);
                break;
        case STATEMENT_BREAK:
        case STATEMENT_NEXT:
                symbolize_expression(ty, scope, s->expression);
                break;
        case STATEMENT_TYPE_DEFINITION:
                define_type(ty, s, scope);
                break;
        case STATEMENT_CLASS_DEFINITION:
                cd = &s->class;

                if (cd->var == NULL) {
                        define_class(ty, s);
                }

                if (!cd->redpilled) {
                        InjectRedpill(ty, s);
                }

                subscope = cd->scope;

                STATE.class = class_get(ty, cd->symbol);

                /*
                for (int i = 0; i < vN(s->class.fields); ++i) {
                        Expr *m = v__(s->class.fields, i);
                        Expr *id = (m->type == EXPRESSION_EQ)
                                 ? m->target
                                 : m;
                        symbolize_expression(ty, s->class.scope, id->constraint);
                        id->_type = type_resolve(ty, id->constraint);
                }
                */

                apply_decorator_macros(ty, subscope, vv(cd->methods), vN(cd->methods));
                apply_decorator_macros(ty, subscope, vv(cd->getters), vN(cd->getters));
                apply_decorator_macros(ty, subscope, vv(cd->setters), vN(cd->setters));
                apply_decorator_macros(ty, subscope, vv(cd->s_methods), vN(cd->s_methods));
                apply_decorator_macros(ty, subscope, vv(cd->s_getters), vN(cd->s_getters));
                apply_decorator_macros(ty, subscope, vv(cd->s_setters), vN(cd->s_setters));

                /*
                 * We have to move all of the operator methods out of the class and just
                 * treat them as top-level operator definitions. We want
                 *
                 *     class Foo {
                 *          <%>(other: Bar) {
                 *              ...
                 *          }
                 *     }
                 *
                 * to be equivalent to
                 *
                 *     class Foo {
                 *     }
                 *
                 *     function <%>(self: Foo, other: Bar) {
                 *          ...
                 *     }
                 *
                 * TODO: Do we want to keep them defined as methods as well? As it stands now, these
                 *       definitions won't be found if you look them up dynamically on an object at runtime
                 *       using member() -- feels a bit leaky
                 */

                {
                        int c = cd->symbol;

                        symbolize_methods(ty, subscope, c, &cd->methods, MT_INSTANCE);
                        symbolize_methods(ty, subscope, c, &cd->getters, MT_GET);
                        symbolize_methods(ty, subscope, c, &cd->setters, MT_SET);
                        symbolize_methods(ty, subscope, c, &cd->s_methods, MT_STATIC);
                        symbolize_methods(ty, subscope, c, &cd->s_getters, MT_STATIC);
                        symbolize_methods(ty, subscope, c, &cd->s_setters, MT_STATIC);

                        symbolize_fields(ty, subscope, &cd->fields);
                        symbolize_fields(ty, subscope, &cd->s_fields);
                }

                STATE.class = NULL;

                break;
        case STATEMENT_TAG_DEFINITION:
                cd = &s->tag;
                symbolize_methods(ty, cd->scope, CLASS_TAG, &s->tag.methods, MT_INSTANCE);
                symbolize_methods(ty, cd->scope, CLASS_TAG, &s->tag.s_methods, MT_STATIC);
                break;
        case STATEMENT_BLOCK:
                scope = scope_new(ty, "(block)", scope, false);
        case STATEMENT_MULTI:
                for (usize i = 0; i < vN(s->statements); ++i) {
                        for (
                                int j = i;

                                j < vN(s->statements)
                             && v__(s->statements, j)->type == STATEMENT_FUNCTION_DEFINITION
                             && v__(s->statements, j)->xscope == NULL;

                                j += 1
                        ) {
                                Stmt *s0 = v__(s->statements, j);
                                symbolize_lvalue(ty, scope, s0->target, true, s0->pub);
                                s0->target->symbol->doc = s0->doc;
                        }

                        symbolize_statement(ty, scope, v__(s->statements, i));
                }
                if (vN(s->statements) > 0) {
                        s->will_return = vvL(s->statements)[0]->will_return;
                        unify(ty, &s->_type, (*vvL(s->statements))->_type);
                }
                if (!WillReturn(s) && s->type == STATEMENT_BLOCK) {
                        avPv(scope->parent->refinements, scope->refinements);
                        v0(scope->refinements);
                }
                break;
        case STATEMENT_TRY:
        {
                begin_try(ty);

                symbolize_statement(ty, scope, s->try.s);

                get_try(ty, 0)->ctx = TRY_CATCH;
                for (int i = 0; i < vN(s->try.patterns); ++i) {
                        Scope *catch = scope_new(ty, "(catch)", scope, false);
                        symbolize_pattern(ty, catch, v__(s->try.patterns, i), NULL, true);
                        symbolize_statement(ty, catch, v__(s->try.handlers, i));
                }

                get_try(ty, 0)->ctx = TRY_CATCH;
                symbolize_statement(ty, scope, s->try.finally);

                s->try.need_trace = end_try(ty)->need_trace;
                break;
        }
        case STATEMENT_MATCH:
                s->will_return = vN(s->match.statements) > 0;
        case STATEMENT_WHILE_MATCH:
        {
                symbolize_expression(ty, scope, s->match.e);

                Type *t0 = s->match.e->_type;

                for (int i = 0; i < vN(s->match.patterns); ++i) {
                        Expr *pat = v__(s->match.patterns, i);
                        subscope = scope_new(ty, "(match-branch)", scope, false);
                        symbolize_pattern(ty, subscope, pat, NULL, true);
                        unify(ty, &t0, pat->_type);
                        symbolize_statement(ty, subscope, v__(s->match.statements, i));
                        t0 = type_without(ty, t0, pat->_type);
                        s->will_return &= v__(s->match.statements, i)->will_return;
                }

                s->_type = type_match_stmt(ty, s);
                SET_TYPE_SRC(s);
                break;
        }
        case STATEMENT_WHILE:
                subscope = scope_new(ty, "(while)", scope, false);
                for (int i = 0; i < vN(s->While.parts); ++i) {
                        struct condpart *p = v__(s->While.parts, i);
                        fix_part(ty, p, scope);
                        symbolize_expression(ty, subscope, p->e);
                        symbolize_pattern(ty, subscope, p->target, NULL, p->def);
                        if (p->target != NULL) {
                                type_assign(ty, p->target, p->e->_type, 0);
                        } else {
                                AddRefinements(ty, p->e, subscope, NULL);
                        }
                }
                symbolize_statement(ty, subscope, s->While.block);
                break;
        case STATEMENT_IF:
                // if not let Ok(x) = f() or not [y] = bar() { ... }
                subscope = scope_new(ty, "(if)", scope, false);
                subscope2 = scope_new(ty, "(if)", scope, false);
                if (s->iff.neg) {
                        symbolize_statement(ty, scope, s->iff.then);
                        for (int i = 0; i < vN(s->iff.parts); ++i) {
                                struct condpart *p = v__(s->iff.parts, i);
                                fix_part(ty, p, scope);
                                WITH_SCOPE_LIMIT(s->when) {
                                        symbolize_pattern(ty, scope, p->target, NULL, p->def);
                                        symbolize_expression(ty, subscope, p->e);
                                        if (p->target != NULL) {
                                                type_assign(ty, p->target, p->e->_type, 0);
                                        }
                                }
                        }
                        symbolize_statement(ty, subscope, s->iff.otherwise);
                } else {
                        for (int i = 0; i < vN(s->iff.parts); ++i) {
                                struct condpart *p = v__(s->iff.parts, i);
                                fix_part(ty, p, scope);
                                symbolize_expression(ty, subscope, p->e);
                                symbolize_pattern(ty, subscope, p->target, NULL, p->def);
                                if (p->target != NULL) {
                                        type_assign(ty, p->target, p->e->_type, 0);
                                }
                                if (p->target == NULL) {
                                        AddRefinements(
                                                ty,
                                                p->e,
                                                subscope,
                                                subscope2
                                        );
                                }
                        }
                        symbolize_statement(ty, subscope2, s->iff.otherwise);
                        symbolize_statement(ty, subscope, s->iff.then);
                        if (WillReturn(s->iff.then) && !WillReturn(s->iff.otherwise)) {
                                avPv(scope->refinements, subscope2->refinements);
                                v0(subscope2->refinements);
                        }
                        if (WillReturn(s->iff.otherwise) && !WillReturn(s->iff.then)) {
                                avPv(scope->refinements, subscope->refinements);
                                v0(subscope->refinements);
                        }
                }
                if (s->iff.then != NULL) {
                        unify(ty, &s->_type, s->iff.then->_type);
                        s->will_return = s->iff.then->will_return;
                } else {
                        unify(ty, &s->_type, NIL_TYPE);
                }
                if (s->iff.otherwise != NULL) {
                        unify(ty, &s->_type, s->iff.otherwise->_type);
                } else {
                        unify(ty, &s->_type, NIL_TYPE);
                }
                s->will_return = (s->iff.then != NULL && s->iff.then->will_return)
                              && (s->iff.otherwise != NULL && s->iff.otherwise->will_return);
                break;
        case STATEMENT_FOR_LOOP:
                scope = scope_new(ty, "(for)", scope, false);
                subscope = scope_new(ty, "(for-body)", scope, false);
                symbolize_statement(ty, scope, s->for_loop.init);
                symbolize_expression(ty, scope, s->for_loop.cond);
                AddRefinements(ty, s->for_loop.cond, subscope, NULL);
                symbolize_statement(ty, subscope, s->for_loop.body);
                symbolize_expression(ty, scope, s->for_loop.next);
                s->_type = s->for_loop.body->_type;
                s->will_return = WillReturn(s->for_loop.body);
                break;
        case STATEMENT_EACH_LOOP:
                symbolize_expression(ty, scope, s->each.array);
                subscope = scope_new(ty, "(for-each)", scope, false);
                symbolize_lvalue(ty, subscope, s->each.target, true, false);
                type_assign_iterable(ty, s->each.target, s->each.array->_type, 0);
                symbolize_statement(ty, subscope, s->each.body);
                symbolize_expression(ty, subscope, s->each.cond);
                symbolize_expression(ty, subscope, s->each.stop);
                s->_type = s->each.body->_type;
                s->will_return = WillReturn(s->each.body);
                break;
        case STATEMENT_RETURN:
                if (STATE.func == NULL) {
                        fail("invalid return statement (not inside of a function)");
                }

                for (int i = 0; i < vN(s->returns); ++i) {
                        symbolize_expression(ty, scope, v__(s->returns, i));
                        dont_printf("  return: %s\n", type_show(ty, v__(s->returns, i)->_type));
                }

                if (STATE.func->type == EXPRESSION_GENERATOR) {
                        s->type = STATEMENT_GENERATOR_RETURN;
                } else if (CheckTypes && STATE.func->_type != NULL) {
                        Type *t0 = (vN(s->returns) == 0) ? NIL_TYPE
                                 : (vN(s->returns) == 1) ? (*vvL(s->returns))->_type
                                 : type_list_from(ty, &s->returns);

                        dont_printf("  before unify: %s\n", type_show(ty, STATE.func->_type->rt));

                        unify2(ty, &STATE.func->_type->rt, t0);

                        if (STATE.func->_type->rt == NULL) {
                                STATE.func->_type->rt = TYPE_ANY;
                        }

                        dont_printf("  after unify: %s\n", type_show(ty, STATE.func->_type->rt));
                }

                s->will_return = true;

                break;
        case STATEMENT_DEFINITION:
                WITH_SCOPE_LIMIT(s->when) {
                        if (s->value->type == EXPRESSION_LIST) {
                                for (int i = 0; i < vN(s->value->es); ++i) {
                                        symbolize_expression(ty, scope, v__(s->value->es, i));
                                }
                        } else {
                                symbolize_expression(ty, scope, s->value);
                        }
                }
                symbolize_lvalue(ty, scope, s->target, true, s->pub);
                type_assign(
                        ty,
                        s->target,
                        s->value->_type,
                        T_FLAG_STRICT | T_FLAG_AVOID_NIL
                );
                if (s->target->type == EXPRESSION_IDENTIFIER) {
                       dont_printf(
                                "%s ::= %s\n",
                                s->target->identifier,
                                type_show(ty, s->target->symbol->type)
                        );
                }
                break;
        case STATEMENT_OPERATOR_DEFINITION:
                symbolize_expression(ty, scope, s->value);
                /*
                 * We can strip away the constraints now. The checks will only ever be
                 * reached when the operands are already known to satisfy them.
                 */
                for (int i = 0; i < vN(s->value->constraints); ++i) {
                        *v_(s->value->constraints, i) = NULL;
                }
                break;
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
                symbolize_lvalue(
                        ty,
                        scope,
                        s->target,
                        HasBody(s->value) && (s->target->module == NULL),
                        s->pub
                );
                symbolize_expression(ty, scope, s->value);
                dont_printf("%s(0) :: %s\n", s->target->identifier, type_show(ty, s->target->symbol->type));
                if (s->value->overload == NULL) {
                        Symbol *var = s->target->symbol;
                        if (HasBody(s->value)) {
                                var->type = s->value->fn_symbol->type;
                        }
                        s->target->_type = s->value->_type;
                        dont_printf("%s(1) :: %s\n", s->target->identifier, type_show(ty, s->target->symbol->type));
                        s->target->symbol->expr = s->value;
                }
                break;
        }

        s->xscope = scope;

        PopScope();
        RestoreContext(ty, ctx);
}

inline static void
patch_jumps_to(offset_vector const *js, usize location)
{
        for (int i = 0; i < js->count; ++i) {
                int distance = location - js->items[i] - sizeof (int);
                memcpy(v_(STATE.code, js->items[i]), &distance, sizeof distance);
        }
}

inline static void
patch_loop_jumps(Ty *ty, usize begin, usize end)
{
        patch_jumps_to(&get_loop(ty, 0)->continues, begin);
        patch_jumps_to(&get_loop(ty, 0)->breaks, end);
}

inline static void
InitJumpGroup(JumpGroup *jg)
{
        v00(*jg);
        jg->label = STATE.label++;
}

inline static char
last_instr(void)
{
        return v__(STATE.code, vN(STATE.code) - 1);
}

inline static void
emit_int(Ty *ty, int k)
{
        LOG("emitting int: %d", k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (int); ++i) {
                avP(STATE.code, s[i]);
        }
}

inline static void
emit_int16(Ty *ty, int16_t k)
{
        LOG("emitting int16_t: %d", (int)k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (int16_t); ++i){
                avP(STATE.code, s[i]);
        }
}

inline static void
emit_ulong(Ty *ty, unsigned long k)
{
        LOG("emitting ulong: %lu", k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (unsigned long); ++i) {
                avP(STATE.code, s[i]);
        }
}

#define emit_symbol(s) ((emit_symbol)(ty, (uptr)(s)))
inline static void
(emit_symbol)(Ty *ty, uptr sym)
{
        LOG("emitting symbol: %"PRIuPTR, sym);
        char const *s = (char *) &sym;
        for (int i = 0; i < sizeof (uptr); ++i) {
                avP(STATE.code, s[i]);
        }
}

inline static void
emit_integer(Ty *ty, intmax_t k)
{

        LOG("emitting integer: %"PRIiMAX, k);
        avPn(STATE.code, (char const *)&k, sizeof k);
}

inline static void
emit_float(Ty *ty, double x)
{
        LOG("emitting float: %f", x);
        avPn(STATE.code, (char const *)&x, sizeof x);
}

inline static void
emit_string(Ty *ty, char const *s)
{
        LOG("emitting string: %s", s);
        usize size = strlen(s) + 1;
        avPn(STATE.code, s, size);
}

#ifndef TY_NO_LOG
#define emit_load_instr(ty, id, inst, i)        \
        do {                                    \
                annotate("%s", id);             \
                (emit_instr)(ty, inst);         \
                Ei32(i);                \
                emit_string(ty, id);            \
        } while (0)
#else
#define emit_load_instr(ty, id, inst, i)        \
        do {                                    \
                annotate("%s", id);             \
                (emit_instr)(ty, inst);         \
                Ei32(i);                \
        } while (0)
#endif

inline static void
target_captured(Ty *ty, Scope const *scope, Symbol const *s)
{
        int i = 0;
        while (v__(scope->function->captured, i) != s) {
                i += 1;
        }

        INSN(TARGET_CAPTURED);
        Ei32(i);
#ifndef TY_NO_LOG
        emit_string(ty, s->identifier);
#endif
}

inline static void
emit_load(Ty *ty, Symbol const *s, Scope const *scope)
{
        LOG("Emitting LOAD for %s", s->identifier);

        bool local = !SymbolIsGlobal(s)
                  && !SymbolIsTypeVar(s)
                  && (s->scope->function == scope->function);

        // Resolved to a class field but then got pulled out
        // of the class to become a global binary operator
        // overload -- gotta use arg0 instead of STATE.self
        bool class_op_self_access = SymbolIsMember(s)
                                 && (STATE.self == NULL);

        if (SymbolIsTypeVar(s)) {
                INSN(BOOLEAN);
                Eu1(true);
        } else if (class_op_self_access) {
                emit_load(ty, v__(STATE.func->param_symbols, 0), scope);
                INSN(MEMBER_ACCESS);
                Ei32(s->member);
        } else if (IsLocalMemberSymbol(ty, s, scope)) {
                INSN(SELF_MEMBER_ACCESS);
                Ei32(s->member);
        } else if (SymbolIsMember(s)) {
                emit_load(ty, STATE.self, scope);
                INSN(MEMBER_ACCESS);
                Ei32(s->member);
        } else if (s->class != -1) {
                INSN(CLASS);
                Ei32(s->class);
        } else if (s == &UndefinedSymbol) {
                INSN(TRAP);
        } else if (SymbolIsThreadLocal(s)) {
                emit_load_instr(ty, s->identifier, INSTR_LOAD_THREAD_LOCAL, s->i);
        } else if (SymbolIsGlobal(s)) {
                emit_load_instr(ty, s->identifier, INSTR_LOAD_GLOBAL, s->i);
                CHECK_INIT();
        } else if (local && !SymbolIsCaptured(s)) {
                emit_load_instr(ty, s->identifier, INSTR_LOAD_LOCAL, s->i);
        } else if (!local && SymbolIsCaptured(s)) {
                int i = 0;
                while (v__(scope->function->captured, i) != s) {
                        i += 1;
                }
                emit_load_instr(ty, s->identifier, INSTR_LOAD_CAPTURED, i);
        } else {
                emit_load_instr(ty, s->identifier, INSTR_LOAD_REF, s->i);
        }
}

inline static void
emit_tgt(Ty *ty, Symbol *s, Scope const *scope, bool def)
{
        bool local = !SymbolIsGlobal(s) && (s->scope->function == scope->function);

        if (s == &UndefinedSymbol) {
                INSN(TRAP);
        } else if (IsLocalMemberSymbol(ty, s, scope)) {
                INSN(TARGET_SELF_MEMBER);
                Ei32(s->member);
        } else if (SymbolIsMember(s)) {
                emit_load(ty, STATE.self, scope);
                INSN(TARGET_MEMBER);
                Ei32(s->member);
        } else if (SymbolIsThreadLocal(s)) {
                INSN(TARGET_THREAD_LOCAL);
                Ei32(s->i);
        } else if (SymbolIsGlobal(s)) {
                INSN(TARGET_GLOBAL);
                Ei32(s->i);
        } else if (def || (local && !SymbolIsCaptured(s))) {
                INSN(TARGET_LOCAL);
                Ei32(s->i);
        } else if (!local && SymbolIsCaptured(s)) {
                target_captured(ty, scope, s);
        } else {
                INSN(TARGET_REF);
                Ei32(s->i);
        }
}

static void
emit_list(Ty *ty, Expr const *e)
{
        INSN(SENTINEL);
        INSN(CLEAR_RC);

        if (e->type == EXPRESSION_LIST) for (int i = 0; i < vN(e->es); ++i) {
                if (is_call(v__(e->es, i))) {
                        INSN(CLEAR_RC);
                        EE(v__(e->es, i));
                        INSN(GET_EXTRA);
                } else {
                        EE(v__(e->es, i));
                }
        } else {
                INSN(CLEAR_RC);
                EE(e);
                INSN(GET_EXTRA);
        }
}

inline static JumpPlaceholder
(PLACEHOLDER_JUMP)(Ty *ty, int insn)
{
        int label = STATE.label++;

        annotate("%sL%d%s", TERM(95), label + 1, TERM(0));

        (emit_instr)(ty, insn);

        JumpPlaceholder jmp = {
                .off = vN(STATE.code),
                .label = label
        };

        Ei32(0);

        return jmp;
}

static JumpPlaceholder
(PLACEHOLDER_JUMP_IF)(Ty *ty, Expr const *e)
{
        JumpPlaceholder jmp;

        switch (e->type) {
        case EXPRESSION_LT:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JLT);

        case EXPRESSION_LEQ:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JLE);

        case EXPRESSION_GT:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JGT);

        case EXPRESSION_GEQ:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JGE);

        case EXPRESSION_DBL_EQ:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JEQ);

        case EXPRESSION_NOT_EQ:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JNE);

        case EXPRESSION_CHECK_MATCH:
                if (IsClassName(e->right)) {
                        EE(e->left);
                        jmp = (PLACEHOLDER_JUMP)(ty, INSTR_JII);
                        Ei32(-e->right->symbol->class);
                        return jmp;
                } else {
                        goto General;
                }
                break;

        default:
        General:
                EE(e);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF);
        }
}

static JumpPlaceholder
(PLACEHOLDER_JUMP_IF_NOT)(Ty *ty, Expr const *e)
{
        JumpPlaceholder jmp;

        switch (e->type) {
        case EXPRESSION_LT:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JGE);

        case EXPRESSION_LEQ:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JGT);

        case EXPRESSION_GT:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JLE);

        case EXPRESSION_GEQ:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JLT);

        case EXPRESSION_DBL_EQ:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JNE);

        case EXPRESSION_NOT_EQ:
                EE(e->left);
                EE(e->right);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JEQ);

        case EXPRESSION_CHECK_MATCH:
                if (IsClassName(e->right)) {
                        EE(e->left);
                        jmp = (PLACEHOLDER_JUMP)(ty, INSTR_JNI);
                        Ei32(-e->right->symbol->class);
                        return jmp;
                } else {
                        goto General;
                }
                break;

        default:
        General:
                EE(e);
                return (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF_NOT);
        }
}

inline static JumpLabel
(LABEL)(Ty *ty)
{
        JumpLabel label = {
                .off = vN(STATE.code),
                .label = STATE.label++
        };

        annotate(":L%d", label.label + 1);

        return label;
}

static void
fail_match_if(Ty *ty, Expr const *e)
{
        switch (e->type) {
        case EXPRESSION_LT:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JLT);
                break;

        case EXPRESSION_LEQ:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JLE);
                break;

        case EXPRESSION_GT:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JGT);
                break;

        case EXPRESSION_GEQ:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JGE);
                break;

        case EXPRESSION_DBL_EQ:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JEQ);
                break;

        case EXPRESSION_NOT_EQ:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JNE);
                break;

        default:
                EE(e);
                FAIL_MATCH_IF(JUMP_IF);
                break;
        }
}

static void
fail_match_if_not(Ty *ty, Expr const *e)
{
        switch (e->type) {
        case EXPRESSION_LT:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JGE);
                break;

        case EXPRESSION_LEQ:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JGT);
                break;

        case EXPRESSION_GT:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JLE);
                break;

        case EXPRESSION_GEQ:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JLT);
                break;

        case EXPRESSION_DBL_EQ:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JNE);
                break;

        case EXPRESSION_NOT_EQ:
                EE(e->left);
                EE(e->right);
                FAIL_MATCH_IF(JEQ);
                break;

        case EXPRESSION_CHECK_MATCH:
                if (IsClassName(e->right)) {
                        EE(e->left);
                        FAIL_MATCH_IF(JNI);
                        Ei32(-e->right->symbol->class);
                } else {
                        goto General;
                }
                break;

        default:
        General:
                EE(e);
                FAIL_MATCH_IF(JUMP_IF_NOT);
                break;
        }
}

static void
_xemit_constraint(Ty *ty, Expr const *c, JumpSet *jumps)
{
        if (c->type == EXPRESSION_TYPE_UNION) {
                for (int i = 0; i < vN(c->es); ++i) {
                        if (i + 1 == vN(c->es)) {
                                _xemit_constraint(ty, v__(c->es, i), jumps);
                        } else {
                                INSN(DUP);
                                _xemit_constraint(ty, v__(c->es, i), jumps);
                                INSN(DUP);
                                svP(*jumps, (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF));
                                INSN(POP);
                        }
                }
        } else {
                EE(c);
                INSN(CHECK_MATCH);
        }
}

static void
emit_constraint(Ty *ty, Expr const *c)
{
        JumpSet jumps = {0};

        SCRATCH_SAVE();

        _xemit_constraint(ty, c, &jumps);

        for (int i = 0; i < vN(jumps); ++i) {
                PATCH_JUMP(v__(jumps, i));
        }

        SCRATCH_RESTORE();
}

static void
emit_assertion(Ty *ty, Expr const *e)
{
        if (STATE.module == GlobalModule) {
                xvP(PreludeAssertionOffsets, vN(STATE.code));
                PLACEHOLDER_JUMP(SKIP_CHECK, skip);
                EE(e);
                INSN(CHECK_MATCH);
                PATCH_JUMP(skip);
        } else {
                EE(e);
                INSN(CHECK_MATCH);
        }
}

static void
add_annotation(Ty *ty, char const *name, uptr start, uptr end)
{
        ProgramAnnotation annotation = STATE.annotation;

        annotation.patched = false;
        annotation.name    = name;
        annotation.module  = CurrentModuleName(ty);
        annotation.start   = start;
        annotation.end     = end;

        xvP(annotations, annotation);
}

static void
PatchAnnotations(Ty *ty)
{
        for (int i = 0; i < vN(annotations); ++i) {
                ProgramAnnotation *annotation = vvL(annotations) - i;

                if (annotation->patched) {
                        /*
                         * We've seen all of the new annotations, everthing from here back
                         * came from an earlier module and has already been patched.
                         */
                        break;
                }

                PatchAnnotation(annotation, vv(STATE.code));
        }
}

static void
emit_function(Ty *ty, Expr const *e)
{
        // =====================================================================
        //
        // Save a bunch of function-related state so we can restore after this
        //
        symbol_vector syms_save = STATE.bound_symbols;
        STATE.bound_symbols.items = e->bound_symbols.items;
        vN(STATE.bound_symbols) = vN(e->bound_symbols);

        LoopStates loops = STATE.loops;
        v00(STATE.loops);

        TryStates tries = STATE.tries;
        v00(STATE.tries);

        int t_save = t;
        t = 0;

        int label_save = STATE.label;
        STATE.label = 0;

        Scope *fs_save = STATE.fscope;
        STATE.fscope = e->scope;

        Expr *func_save = STATE.func;
        STATE.func = (Expr *)e;
        // =====================================================================

        Symbol **caps        = vv(e->scope->captured);
        int     *cap_indices = vv(e->scope->cap_indices);
        int      ncaps       = vN(e->scope->captured);
        int      bound_caps  = 0;

        LOG("Compiling %s. scope=%s", e->name == NULL ? "(anon)" : e->name, scope_name(ty, e->scope));

        for (int i = ncaps - 1; i >= 0; --i) {
                if (caps[i]->scope->function == e->scope) {
                        bound_caps += 1;
                } else if (cap_indices[i] == -1) {
                        /*
                         * Don't call emit_tgt because despite these being captured,
                         * we need to use TARGET_LOCAL to avoid following the reference.
                         */
                        annotate("%s", caps[i]->identifier);
                        INSN(TARGET_LOCAL);
                        Ei32(caps[i]->i);
                } else {
                        // FIXME: should just use same allocated variable
                        annotate("%s", caps[i]->identifier);
                        INSN(TARGET_CAPTURED);
                        Ei32(cap_indices[i]);
#ifndef TY_NO_LOG
                        emit_string(ty, caps[i]->identifier);
#endif
                }
        }

        // ====/ New function /=================================================
        INSN(FUNCTION);

        while (!IS_ALIGNED_FOR(int, vec_last(STATE.code) + 1)) {
                avP(STATE.code, 0);
        }

        Ei32(bound_caps);

        int bound = vN(e->scope->owned);

        usize hs_offset = vN(STATE.code);
        Ei32(0);

        usize size_offset = vN(STATE.code);
        Ei32(0);

        Ei32(ncaps);
        Ei32(bound);
        Ei32(vN(e->param_symbols));
        emit_int16(ty, e->rest);
        emit_int16(ty, e->ikwargs);

        for (int i = 0; i < sizeof (int) - 2 * sizeof (int16_t); ++i) {
                avP(STATE.code, 0);
        }

        Ei32(e->class);

        // Need to GC code?
        avP(STATE.code, GetArenaAlloc(ty) != NULL);

        // Is this function hidden (i.e. omitted from stack trace messages)?
        avP(STATE.code, e->type == EXPRESSION_MULTI_FUNCTION);

        emit_symbol(e->proto);
        emit_symbol(e->doc);

        char const *fun_name;

        if (e->name != NULL) {
                fun_name = e->name;
        } else if (!CheckTypes) {
                fun_name = "(anonymous function)";
        } else {
                char buffer[512];
                snprintf(
                        buffer,
                        sizeof buffer,
                        "(anonymous function : %s:%d)",
                        CurrentModuleName(ty),
                        e->start.line + 1
                );
                fun_name = sclonea(ty, buffer);
        }

        emit_symbol(fun_name);
        emit_symbol(e);

        LOG("COMPILING FUNCTION: %s", scope_name(ty, e->scope));

        for (int i = 0; i < ncaps; ++i) {
                LOG(" => CAPTURES %s", caps[i]->identifier);
        }

        for (int i = 0; i < vN(e->param_symbols); ++i) {
                emit_string(ty, v__(e->param_symbols, i)->identifier);
        }

        int hs = vN(STATE.code) - hs_offset;
        memcpy(v_(STATE.code, hs_offset), &hs, sizeof hs);

        /*
         * Remember where in the code this function's code begins so that we can compute
         * the relative offset of references to non-local variables.
         */
        usize start_offset = vN(STATE.code);

        for (int i = 0; i < vN(e->param_symbols); ++i) {
                if (
                        (v__(e->dflts, i) == NULL)
                     || (v__(e->dflts, i)->type == EXPRESSION_NIL)
                ) {
                        continue;
                }
                Symbol const *s = v__(e->param_symbols, i);
                emit_load_instr(ty, s->identifier, INSTR_LOAD_LOCAL, s->i);
                PLACEHOLDER_JUMP(JUMP_IF_NIL, need_dflt);
                PLACEHOLDER_JUMP(JUMP, skip_dflt);
                PATCH_JUMP(need_dflt);
                annotate("%s", s->identifier);
                EE(v__(e->dflts, i));
                INSN(ASSIGN_LOCAL);
                Ei32(s->i);
                PATCH_JUMP(skip_dflt);
        }

        for (int i = 0; i < vN(e->param_symbols); ++i) {
                if (
                        (v__(e->constraints, i) == NULL)
                     || (
                                !RUNTIME_CONSTRAINTS
                             && (e->overload == NULL)
                        )
                ) {
                        continue;
                }

                Symbol const *s = v__(e->param_symbols, i);
                usize start = vN(STATE.code);

                emit_load_instr(ty, s->identifier, INSTR_LOAD_LOCAL, s->i);

                if (e->overload != NULL) {
                        EC(v__(e->constraints, i));
                        PLACEHOLDER_JUMP(JUMP_IF, good);
                        INSN(POP);
                        INSN(NONE);
                        INSN(RETURN);
                        PATCH_JUMP(good);
                } else {
                        EA(v__(e->constraints, i));
                        PLACEHOLDER_JUMP(JUMP_IF, good);
                        emit_load_instr(ty, s->identifier, INSTR_LOAD_LOCAL, s->i);
                        INSN(BAD_CALL);
                        emit_string(ty, fun_name);
                        emit_string(ty, v__(e->param_symbols, i)->identifier);
                        add_location(ty, v__(e->constraints, i), start, vN(STATE.code));
                        INSN(POP);
                        PATCH_JUMP(good);
                }
        }

        int   function_resources = STATE.function_resources;
        STATE.function_resources = STATE.resources;

        Stmt *body = e->body;

        if (e->has_defer) {
                Stmt  *try  = NewStmt(ty, STATEMENT_TRY_CLEAN);
                try->start  = body->start;
                try->end    = body->end;
                try->try.s  = body;

                Stmt  *cleanup = NewStmt(ty, STATEMENT_CLEANUP);
                cleanup->start = body->start;
                cleanup->end   = body->end;

                try->try.finally = cleanup;

                body = try;
        }

        if (e->type == EXPRESSION_GENERATOR) {
                INSN(MAKE_GENERATOR);
                emit_statement(ty, body, false);
                LABEL(end);
                INSN(YIELD_NONE);
                INSN(POP);
                JUMP(end);
                patch_jumps_to(&STATE.generator_returns, end.off);
        } else if (e->type == EXPRESSION_MULTI_FUNCTION) {
                for (int i = 0; i < vN(e->functions); ++i) {
                        Expr *f = *v_(e->functions, i);
                        if (!is_method(e)) {
                                INSN(SAVE_STACK_POS);
                                emit_load_instr(ty, "[@]", INSTR_LOAD_LOCAL, 0);
                                emit_spread(ty, NULL, false);
                                emit_load_instr(ty, "[%]", INSTR_LOAD_LOCAL, 1);
                                emit_load_instr(ty, "", INSTR_LOAD_GLOBAL, ((Stmt *)f)->target->symbol->i);
                                CHECK_INIT();
                                INSN(CALL);
                                Ei32(-1);
                                Ei32(1);
                                emit_string(ty, "*");
                                INSN(RETURN_IF_NOT_NONE);
                                INSN(POP);
                        } else if (e->mtype == MT_SET) {
                                emit_load_instr(ty, "[@]", INSTR_LOAD_LOCAL, 0);
                                emit_load_instr(ty, "self", INSTR_LOAD_LOCAL, 1);
                                INSN(TARGET_MEMBER);
                                emit_member(ty, f->name);
                                INSN(ASSIGN);
                                INSN(RETURN_IF_NOT_NONE);
                                INSN(POP);
                        } else {
                                INSN(SAVE_STACK_POS);
                                emit_load_instr(ty, "[@]", INSTR_LOAD_LOCAL, 0);
                                emit_spread(ty, NULL, false);
                                emit_load_instr(ty, "[%]", INSTR_LOAD_LOCAL, 1);
                                emit_load_instr(ty, "self", INSTR_LOAD_LOCAL, 2);
                                INSN(CALL_METHOD);
                                Ei32(-1);
                                emit_member(ty, f->name);
                                Ei32(1);
                                emit_string(ty, "*");
                                INSN(RETURN_IF_NOT_NONE);
                                INSN(POP);
                        }
                }
                INSN(BAD_DISPATCH);
        } else {
                for (int i = ncaps - 1; i >= 0; --i) {
                        if (caps[i]->scope->function == e->scope) {
                                INSN(CAPTURE);
                                Ei32(caps[i]->i);
                                Ei32(i);
                        }
                }
                emit_statement(ty, body, true);
                if (RUNTIME_CONSTRAINTS && e->return_type != NULL) {
                        emit_return_check(ty, e);
                }
                INSN(RETURN);
        }

        STATE.function_resources = function_resources;

        // TODO: what to do here?
        //add_annotation(ty, e->proto, start_offset, vN(STATE.code));

        int bytes = vN(STATE.code) - start_offset;
        memcpy(v_(STATE.code, size_offset), &bytes, sizeof bytes);
        LOG("bytes in func = %d", bytes);

        int self_cap = -1;

        for (int i = 0; i < ncaps; ++i) {
                if (caps[i]->scope->function == e->scope)
                        continue;
                if (caps[i] == e->fn_symbol) {
                        LOG("Function '%s' self-captures at i=%d", fun_name, i);
                        self_cap = i;
                }
                bool local = caps[i]->scope->function == fs_save;
                LOG("local(%s, %s): %d", fun_name, caps[i]->identifier, local);
                LOG("  fscope(%s) = %p, fs_save = %p", caps[i]->identifier, caps[i]->scope->function, fs_save);
                Eu1(local);
                Ei32(i);
        }

        //STATE.annotation = annotation;
        STATE.label          = label_save;
        STATE.fscope         = fs_save;
        STATE.bound_symbols  = syms_save;
        STATE.loops          = loops;
        STATE.tries          = tries;
        t                    = t_save;
        // ===========/ Back to parent function /===============================

        LOG("STATE.fscope: %s", scope_name(ty, STATE.fscope));

        if (self_cap != -1) {
                INSN(PATCH_ENV);
                Ei32(self_cap);
        }

        STATE.func = func_save;

        if (vN(e->decorators) > 0) {
                FunUserInfo *info = mAo0(sizeof (FunUserInfo), GC_ANY);
                info->name  = (char *)fun_name;
                info->proto = (char *)e->proto;
                info->doc   = (char *)e->doc;
                NOGC(info);

                for (int i = 0; i < vN(e->decorators); ++i) {
                        Expr *dec = v__(e->decorators, i);
                        EE(dec);
                        INSN(DECORATE);
                        emit_symbol(info);
                }
        }

        if (e->fn_symbol != NULL && e->class == -1) {
                emit_tgt(ty, e->fn_symbol, e->scope->parent, false);
                INSN(ASSIGN);
        }
}

static void
emit_and(Ty *ty, Expr const *left, Expr const *right)
{
        EE(left);
        PLACEHOLDER_JUMP(JUMP_AND, left_false);
        EE(right);
        PATCH_JUMP(left_false);
}

static void
emit_or(Ty *ty, Expr const *left, Expr const *right)
{
        EE(left);
        PLACEHOLDER_JUMP(JUMP_OR, left_true);
        EE(right);
        PATCH_JUMP(left_true);
}

static void
emit_coalesce(Ty *ty, Expr const *left, Expr const *right)
{
        EE(left);
        PLACEHOLDER_JUMP(JUMP_WTF, left_good);
        EE(right);
        PATCH_JUMP(left_good);
}

static void
emit_lang_string(Ty *ty, Expr const *e)
{
        INSN(SAVE_STACK_POS);

        if (v__(e->strings, 0)[0] != '\0') {
                INSN(STRING);
                emit_string(ty, v__(e->strings, 0));
        }

        for (int i = 0; i < vN(e->expressions); ++i) {
                Expr const  *fmt = *v_(e->fmts, i);
                Expr const   *ex = *v_(e->expressions, i);
                int        width = *v_(e->widths, i);

                EE(ex);
                if (fmt == NULL) {
                        INSN(NIL);
                } else {
                        EE(fmt);
                }
                INSN(INTEGER);
                emit_integer(ty, width);
                INSN(TUPLE);
                Ei32(3);
                Ei32(-1);
                Ei32(-1);
                Ei32(-1);

                if (v__(e->strings, i + 1)[0] != '\0') {
                        INSN(STRING);
                        emit_string(ty, v__(e->strings, i + 1));
                }
        }

        INSN(ARRAY);

        EE(e->lang);
        INSN(CALL);
        Ei32(1);
        Ei32(0);
}

static void
emit_special_string(Ty *ty, Expr const *e)
{
        int n = vN(e->expressions);

        if (v__(e->strings, 0)[0] != '\0') {
                INSN(STRING);
                emit_string(ty, v__(e->strings, 0));
                n += 1;
        }

        for (int i = 1; i < vN(e->strings); ++i) {
                if (v__(e->strings, i)[0] != '\0') {
                        n += 1;
                }
        }

        for (int i = 0; i < vN(e->expressions); ++i) {
                Expr const  *fmt = *v_(e->fmts, i);
                Expr const  *arg = *v_(e->fmtfs, i);
                Expr const   *ex = *v_(e->expressions, i);
                int        width = *v_(e->widths, i);

                if (fmt == NULL) {
                        EE(ex);
                        INSN(TO_STRING);
                } else {
                        EE(fmt);

                        INSN(INTEGER);
                        emit_integer(ty, width);

                        EE(ex);

                        INSN(CALL_METHOD);
                        Ei32(2);
                        Ei32(NAMES.fmt);
                        Ei32(0);
                }

                if (arg != NULL) {
                        EE(arg);
                        INSN(CALL);
                        Ei32(1);
                        Ei32(0);
                }

                if (v__(e->strings, i + 1)[0] != '\0') {
                        INSN(STRING);
                        emit_string(ty, v__(e->strings, i + 1));
                }
        }

        if (n > 1) {
                INSN(CONCAT_STRINGS);
                Ei32(n);
        } else if (n == 0) {
                INSN(STRING);
                avP(STATE.code, '\0');
        }
}

static void
emit_with(Ty *ty, Expr const *e)
{
        emit_statement(ty, e->with.block, true);
}

static void
emit_yield(Ty *ty, Expr const * const *es, int n, bool wrap)
{
        if (STATE.func == NULL) {
                fail("invalid yield expression (not inside of a function)");
        }

        if (n > 1) {
                fail("yielding multiple values isn't implemented yet");
        }

        for (int i = 0; i < n; ++i) {
                EE(es[i]);
        }

        (emit_instr)(ty, wrap ? INSTR_YIELD_SOME : INSTR_YIELD);
}

static void
emit_return_check(Ty *ty, Expr const *f)
{
        usize start = vN(STATE.code);

        INSN(DUP);
        EA(f->return_type);
        PLACEHOLDER_JUMP(JUMP_IF, good);
        INSN(BAD_CALL);

        if (f->name != NULL) {
                emit_string(ty, f->name);
        } else {
                emit_string(ty, "(anonymous function)");
        }

        emit_string(ty, "return value");

        add_location(ty, f->return_type, start, vN(STATE.code));

        PATCH_JUMP(good);
}

static bool
emit_return(Ty *ty, Stmt const *s)
{
        if (get_try_ctx(ty) == TRY_FINALLY) {
                fail("invalid return statement (occurs in a finally block)");
        }

        /* returning from within a for-each loop must be handled specially */
        for (int i = 0; i < vN(STATE.loops); ++i) {
                u32 n = get_loop(ty, i)->n;
                while (n --> 0) {
                        INSN(POP);
                }
        }

        Expr **rets = vv(s->returns);
        int nret = vN(s->returns);

        // Tail call optimization -- currently quite restricted :)
        if (
                (nret == 1)
             && (vN(STATE.tries) == 0)
             && (STATE.function_resources == STATE.resources)
             && (!RUNTIME_CONSTRAINTS || STATE.func->return_type == NULL)
             && is_call(rets[0])
             && !is_variadic(rets[0])
             && (rets[0]->function->type == EXPRESSION_IDENTIFIER)
             && (rets[0]->function->symbol == STATE.func->fn_symbol)
             && (vN(rets[0]->args) == vN(STATE.func->params))
             && (vN(rets[0]->kwargs) == 0)
        ) {
                for (int i = 0; i < vN(rets[0]->args); ++i) {
                        EE(v__(rets[0]->args, i));
                }

                INSN(TAIL_CALL);

                return true;
        }

        if (vN(s->returns) > 0) for (int i = 0; i < vN(s->returns); ++i) {
                EE(v__(s->returns, i));
        } else {
                INSN(NIL);
        }

        for (int i = 0; get_try(ty, i) != NULL; ++i) {
                INSN(FINALLY);
        }

        for (int i = STATE.function_resources; i < STATE.resources; ++i) {
                INSN(DROP);
        }

        if (RUNTIME_CONSTRAINTS && STATE.func->return_type != NULL) {
                emit_return_check(ty, STATE.func);
        }

        if (vN(s->returns) > 1) {
                INSN(MULTI_RETURN);
                Ei32((int)vN(s->returns) - 1);
        } else {
                INSN(RETURN);
        }

        return true;
}

static bool
emit_super(Ty *ty, Expr const *e)
{
        char const *func_name = STATE.func->overload != NULL
                              ? STATE.func->overload->name
                              : STATE.func->name;

        int c = class_get_super(ty, CurrentClassID);
        if (c == -1) {
                fail(
                        "%ssuper%s used in %sObject%s?",
                        TERM(95;1), TERM(0),
                        TERM(95;1), TERM(0)
                );
        }

        if (e->symbol != NULL) {
                emit_load(ty, e->symbol, STATE.fscope);
        }

        switch (STATE.meth->mtype) {
        case MT_INSTANCE: INSN(BIND_INSTANCE); break;
        case MT_GET:      INSN(BIND_GETTER);   break;
        case MT_SET:      INSN(BIND_SETTER);   break;
        case MT_STATIC:   INSN(BIND_STATIC);   break;
        }

        Ei32(c);
        emit_member(ty, func_name);

        return false;
}

static bool
emit_try(Ty *ty, Stmt const *s, bool want_result)
{
        INSN(TRY);

        usize catch_offset = vN(STATE.code);
        Ei32(0);

        usize finally_offset = vN(STATE.code);
        Ei32(-1);

        usize end_offset = vN(STATE.code);
        Ei32(-1);

        begin_try(ty);

        if (s->type == STATEMENT_TRY_CLEAN) {
                INSN(PUSH_DEFER_GROUP);
        }

        bool returns = emit_statement(ty, s->try.s, want_result);

        PLACEHOLDER_JUMP(JUMP, finally);

        offset_vector successes_save = STATE.match_successes;
        v00(STATE.match_successes);

        PATCH_OFFSET(catch_offset);

        get_try(ty, 0)->ctx = TRY_CATCH;

        for (int i = 0; i < vN(s->try.patterns); ++i) {
                returns &= emit_catch(
                        ty,
                        v__(s->try.patterns, i),
                        NULL,
                        v__(s->try.handlers, i),
                        want_result
                );
        }

        INSN(RETHROW);

        patch_jumps_to(&STATE.match_successes, vN(STATE.code));
        STATE.match_successes = successes_save;

        INSN(CATCH);

        PATCH_JUMP(finally);
        PATCH_OFFSET(finally_offset);

        if (s->try.finally != NULL) {
                get_try(ty, 0)->ctx = TRY_FINALLY;
                returns &= emit_statement(ty, s->try.finally, false);
        }

        INSN(END_TRY);

        PATCH_OFFSET(end_offset);

        end_try(ty);

        return returns;
}

static void
emit_for_loop(Ty *ty, Stmt const *s, bool want_result)
{
        begin_loop(ty, want_result, 0);

        if (s->for_loop.init != NULL) {
                emit_statement(ty, s->for_loop.init, false);
        }

        PLACEHOLDER_JUMP(JUMP, skip_next);

        LABEL(begin);

        if (s->for_loop.next != NULL) {
                EE(s->for_loop.next);
                INSN(POP);
        }

        PATCH_JUMP(skip_next);

        JumpPlaceholder end_jump;
        if (s->for_loop.cond != NULL) {
                end_jump = (PLACEHOLDER_JUMP_IF_NOT)(ty, s->for_loop.cond);
        }

        emit_statement(ty, s->for_loop.body, false);

        JUMP(begin);

        if (s->for_loop.cond != NULL) {
                PATCH_JUMP(end_jump);
        }

        if (want_result) {
                INSN(NIL);
        }

        patch_loop_jumps(ty, begin.off, vN(STATE.code));

        end_loop(ty);
}

static void
emit_record_rest(Ty *ty, Expr const *rec, int i, bool is_assignment)
{
        emit_tgt(ty, v__(rec->es, i)->symbol, STATE.fscope, true);

        usize bad_assign_jump;

        if (!is_assignment) {
                FAIL_MATCH_IF(RECORD_REST);
        } else {
                INSN(RECORD_REST);
                bad_assign_jump = vN(STATE.code);
                Ei32(0);
        }

        while (!IS_ALIGNED_FOR(int, vec_last(STATE.code) + 1)) {
                avP(STATE.code, 0);
        }

        for (int j = 0; j < i; ++j) {
                if (v__(rec->names, j) != NULL) {
                        Ei32(intern(&xD.members, v__(rec->names, j))->id);
                }
        }

        Ei32(-1);

        if (is_assignment) {
                INSN(JUMP);
                Ei32(1);
                PATCH_OFFSET(bad_assign_jump);
                INSN(BAD_MATCH);
        }
}

static void
emit_try_match_(Ty *ty, Expr const *pattern)
{
        usize    start = vN(STATE.code);
        bool   need_loc = false;
        bool        set = true;
        bool      after = false;

        switch (pattern->type) {
        case EXPRESSION_MATCH_ANY:
                break;
        case EXPRESSION_RESOURCE_BINDING:
                INSN(PUSH_DROP);
                /* fallthrough */
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_ALIAS_PATTERN:
                if (strcmp(pattern->identifier, "_") == 0) {
                        /* nothing to do */
                } else {
                        emit_tgt(ty, pattern->symbol, STATE.fscope, true);
                        INSN(ASSIGN);
                }
                if (pattern->constraint != NULL) {
                        if (IsClassName(pattern->constraint)) {
                                FAIL_MATCH_IF(JNI);
                                Ei32(pattern->constraint->symbol->class);
                        } else {
                                INSN(DUP);
                                EC(pattern->constraint);
                                FAIL_MATCH_IF(JUMP_IF_NOT);
                        }
                }
                if (pattern->type == EXPRESSION_ALIAS_PATTERN) {
                        emit_try_match_(ty, pattern->aliased);
                }
                break;
        case EXPRESSION_TAG_PATTERN:
                emit_tgt(ty, pattern->symbol, STATE.fscope, true);
                FAIL_MATCH_IF(TRY_STEAL_TAG);
                emit_try_match_(ty, pattern->tagged);
                break;
        case EXPRESSION_CHECK_MATCH:
                emit_try_match_(ty, pattern->left);
                if (IsClassName(pattern->right)) {
                        FAIL_MATCH_IF(JNI);
                        Ei32(pattern->right->symbol->class);
                } else {
                        INSN(DUP);
                        EC(pattern->right);
                        FAIL_MATCH_IF(JUMP_IF_NOT);
                }
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_tgt(ty, pattern->symbol, STATE.fscope, true);
                FAIL_MATCH_IF(TRY_ASSIGN_NON_NIL);
                break;
        case EXPRESSION_MUST_EQUAL:
                emit_load(ty, pattern->symbol, STATE.fscope);
                FAIL_MATCH_IF(ENSURE_EQUALS_VAR);
                need_loc = true;
                break;
        case EXPRESSION_KW_AND:
                emit_try_match_(ty, pattern->left);
                for (int i = 0; i < vN(pattern->p_cond); ++i) {
                        struct condpart *p = v__(pattern->p_cond, i);
                        if (p->target == NULL) {
                                fail_match_if_not(ty, p->e);
                        } else {
                                EE(p->e);
                                emit_try_match_(ty, p->target);
                                INSN(POP);
                        }
                }
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                INSN(DUP);
                FAIL_MATCH_IF(JUMP_IF_NIL);
                // Fallthrough
        case EXPRESSION_VIEW_PATTERN:
                INSN(DUP);
                EE(pattern->left);
                INSN(CALL);
                Ei32(1);
                Ei32(0);
                add_location(ty, pattern->left, start, vN(STATE.code));
                emit_try_match_(ty, pattern->right);
                INSN(POP);
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < vN(pattern->elements); ++i) {
                        if (v__(pattern->elements, i)->type == EXPRESSION_MATCH_REST) {
                                if (after) {
                                        PushContext(ty, v__(pattern->elements, i));
                                        fail("array pattern cannot contain multiple gather elements");
                                } else {
                                        after = true;
                                }
                                emit_tgt(ty, v__(pattern->elements, i)->symbol, STATE.fscope, true);
                                FAIL_MATCH_IF(ARRAY_REST);
                                Ei32(i);
                                Ei32(vN(pattern->elements) - i - 1);
                        } else {
                                FAIL_MATCH_IF(TRY_INDEX);
                                if (after) {
                                        if (v__(pattern->optional, i)) {
                                                PushContext(ty, v__(pattern->elements, i));
                                                fail("optional element cannot come after a gather element in array pattern");
                                        }
                                        Ei32(i - vN(pattern->elements));
                                } else {
                                        Ei32(i);
                                }
                                Eu1(!v__(pattern->optional, i));

                                emit_try_match_(ty, v__(pattern->elements, i));

                                INSN(POP);
                        }
                }

                if (!after) {
                        FAIL_MATCH_IF(ENSURE_LEN);
                        Ei32(vN(pattern->elements));
                }

                break;
        case EXPRESSION_DICT:
                /*
                 * If there are only keys and no values, we interpret this as a Set
                 * pattern and just test equality. Otherwise any keys without values
                 * must be present, but they don't need to be the *only* entries.
                 *
                 *  e.g., { [4], 10, "foo" } will only match the Dict containing exactly
                 *      those 3 values.
                 *
                 *      Meanwhile, { [4], 10, "foo": f } matches any Dict containing [4]
                 *      and 10. "foo" doesn't need to be present because `f` is allowed to be
                 *      nil. { [4], 10, "foo": $f } would require the key "foo" to be present.
                 */
                for (int i = 0; i < vN(pattern->keys); ++i) {
                        if (v__(pattern->values, i) != NULL) {
                                set = false;
                                break;
                        }
                }
                if (set) {
                        EE(pattern);
                        FAIL_MATCH_IF(ENSURE_SAME_KEYS);
                } else {
                        FAIL_MATCH_IF(ENSURE_DICT);
                        for (int i = 0; i < vN(pattern->keys); ++i) {
                                if (v__(pattern->values, i) != NULL) {
                                        INSN(DUP);
                                        EE(v__(pattern->keys, i));
                                        INSN(SUBSCRIPT);
                                        emit_try_match_(ty, v__(pattern->values, i));
                                        INSN(POP);
                                } else {
                                        EE(v__(pattern->keys, i));
                                        FAIL_MATCH_IF(ENSURE_CONTAINS);
                                }
                        }
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                INSN(DUP);
                FAIL_MATCH_IF(TRY_TAG_POP);
                Ei32(tag_app_tag(pattern));

                emit_try_match_(ty, pattern->tagged);

                INSN(POP);
                break;
        case EXPRESSION_REGEX:
                FAIL_MATCH_IF(TRY_REGEX);
                emit_symbol((uptr) pattern->regex);
                emit_tgt(ty, (Symbol *)pattern->match_symbol, STATE.fscope, true);
                INSN(ASSIGN_REGEX_MATCHES);
                Ei32(pattern->regex->ncap);
                need_loc = true;
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < vN(pattern->es); ++i) {
                        if (v__(pattern->es, i)->type == EXPRESSION_MATCH_REST) {
                                if (has_any_names(pattern)) {
                                        emit_record_rest(ty, pattern, i, false);
                                } else {
                                        emit_tgt(ty, v__(pattern->es, i)->symbol, STATE.fscope, true);
                                        FAIL_MATCH_IF(TUPLE_REST);
                                        Ei32(i);
                                        if (i + 1 != vN(pattern->es)) {
                                                fail(
                                                        "the *<id> tuple-matching pattern must"
                                                        " be the last pattern in the tuple"
                                                );
                                        }
                                }
                        } else if (v__(pattern->names, i) != NULL) {
                                FAIL_MATCH_IF(TRY_TUPLE_MEMBER);
                                Eu1(v__(pattern->required, i));
                                Ei32(M_ID(v__(pattern->names, i)));
                                emit_try_match_(ty, v__(pattern->es, i));
                                INSN(POP);
                        } else {
                                FAIL_MATCH_IF(TRY_INDEX_TUPLE);
                                Ei32(i);
                                emit_try_match_(ty, v__(pattern->es, i));
                                INSN(POP);
                        }
                }

                if (
                        vN(pattern->es) == 0
                     || vvL(pattern->es)[0]->type != EXPRESSION_MATCH_REST
                ) {
                        FAIL_MATCH_IF(ENSURE_LEN_TUPLE);
                        Ei32(vN(pattern->es));
                }

                break;
        case EXPRESSION_LIST:
        {
                int n = vN(pattern->es);

                INSN(FIX_TO);
                Ei32(n);

                for (int i = 0; i < n; ++i) {
                        emit_try_match_(ty, v__(pattern->es, n - 1 - i));
                        INSN(POP);
                }

                break;
        }
        case EXPRESSION_REF_PATTERN:
        {
                emit_tgt(ty, pattern->tmp, STATE.fscope, true);
                INSN(ASSIGN);
                avP(STATE.match_assignments, pattern);
                break;
        }
        case EXPRESSION_CHOICE_PATTERN:
        {
                vec(JumpPlaceholder) matched = {0};

                INSN(SAVE_STACK_POS);

                for (int i = 0; i < vN(pattern->es); ++i) {
                        JumpGroup fails_save = STATE.match_fails;
                        InitJumpGroup(&STATE.match_fails);

                        emit_try_match_(ty, v__(pattern->es, i));
                        avP(matched, (PLACEHOLDER_JUMP)(ty, INSTR_JUMP));

                        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
                        patch_jumps_to(&STATE.match_fails, vN(STATE.code));

                        if (v_(pattern->es, i) == vvL(pattern->es)) {
                                INSN(POP_STACK_POS);
                        } else {
                                INSN(RESTORE_STACK_POS);
                        }

                        STATE.match_fails = fails_save;
                }

                FAIL_MATCH_IF(JUMP);

                for (int i = 0; i < vN(matched); ++i) {
                        PATCH_JUMP(v__(matched, i));
                }

                INSN(POP_STACK_POS);

                break;
        }
        default:
                /*
                 * Need to think about how this should work...
                 */
                INSN(DUP);
                EE(pattern);
                //INSN(CHECK_MATCH);
                FAIL_MATCH_IF(JNE);
                need_loc = true;
        }

        if (KEEP_LOCATION(pattern) || need_loc) {
                add_location(ty, pattern, start, vN(STATE.code));
        }
}

static void
emit_try_match(Ty *ty, Expr const *pattern)
{
        emit_try_match_(ty, pattern);
}

static bool
emit_catch(Ty *ty, Expr const *pattern, Expr const *cond, Stmt const *s, bool want_result)
{
        JumpGroup fails_save = STATE.match_fails;
        InitJumpGroup(&STATE.match_fails);

        INSN(SAVE_STACK_POS);
        emit_try_match(ty, pattern);

        if (cond != NULL) {
                fail_match_if_not(ty, cond);
        }

        INSN(POP_STACK_POS);
        INSN(CLEAR_EXTRA);

        bool returns = false;

        if (s != NULL) {
                returns = emit_statement(ty, s, want_result);
        } else if (want_result) {
                INSN(NIL);
        }

        INSN(JUMP);
        avP(STATE.match_successes, vN(STATE.code));
        Ei32(0);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));

        INSN(POP_STACK_POS);

        STATE.match_fails = fails_save;

        return returns;
}

static bool
emit_case(Ty *ty, Expr const *pattern, Expr const *cond, Stmt const *s, bool want_result)
{
        if (pattern->type == EXPRESSION_LIST) {
                bool returns = false;
                for (int i = 0; i < vN(pattern->es); ++i) {
                        returns = emit_case(ty, v__(pattern->es, i), NULL, s, want_result);
                }
                return returns;
        }

        JumpGroup fails_save = STATE.match_fails;
        InitJumpGroup(&STATE.match_fails);

        expression_vector assignments = STATE.match_assignments;
        v00(STATE.match_assignments);

        if (pattern->has_resources) {
                INSN(PUSH_DROP_GROUP);
                STATE.resources += 1;
        }

        INSN(SAVE_STACK_POS);
        emit_try_match(ty, pattern);
        if (cond != NULL) {
                fail_match_if_not(ty, cond);
        }
        INSN(POP_STACK_POS_POP);

        bool returns = false;

        for (int i = 0; i < vN(STATE.match_assignments); ++i) {
                Expr *e = *v_(STATE.match_assignments, i);
                emit_load(ty, e->tmp, STATE.fscope);
                emit_assignment2(ty, e->target, false, false);
                INSN(POP);
        }

        if (s != NULL) {
                returns = emit_statement(ty, s, want_result);
        } else if (want_result) {
                INSN(NIL);
        }

        if (pattern->has_resources) {
                INSN(DROP);
        }

        INSN(JUMP);
        avP(STATE.match_successes, vN(STATE.code));
        Ei32(0);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));
        INSN(POP_STACK_POS);

        if (pattern->has_resources) {
                INSN(DISCARD_DROP_GROUP);
                STATE.resources -= 1;
        }

        STATE.match_fails = fails_save;
        STATE.match_assignments = assignments;

        return returns;
}

static void
emit_expression_case(Ty *ty, Expr const *pattern, Expr const *e)
{
        if (pattern->type == EXPRESSION_LIST) {
                for (int i = 0; i < vN(pattern->es); ++i) {
                        emit_expression_case(ty, v__(pattern->es, i), e);
                }
                return;
        }

        JumpGroup fails_save = STATE.match_fails;
        InitJumpGroup(&STATE.match_fails);

        expression_vector assignments = STATE.match_assignments;
        v00(STATE.match_assignments);

        if (pattern->has_resources) {
                INSN(PUSH_DROP_GROUP);
                STATE.resources += 1;
        }

        INSN(SAVE_STACK_POS);
        emit_try_match(ty, pattern);

        /*
         * Go back to where the subject of the match is on top of the stack,
         * then pop it and execute the code to produce the result of this branch.
         */
        INSN(POP_STACK_POS_POP);

        for (int i = 0; i < vN(STATE.match_assignments); ++i) {
                Expr *e = *v_(STATE.match_assignments, i);
                emit_load(ty, e->tmp, STATE.fscope);
                emit_assignment2(ty, e->target, false, false);
        }

        EE(e);

        if (pattern->has_resources) {
                INSN(DROP);
        }

        /*
         * We've successfully matched a pattern+condition and produced a result, so we jump
         * to the end of the match expression. i.e., there is no fallthrough.
         */
        INSN(JUMP);
        avP(STATE.match_successes, vN(STATE.code));
        Ei32(0);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));
        INSN(POP_STACK_POS);

        if (pattern->has_resources) {
                INSN(DISCARD_DROP_GROUP);
                STATE.resources -= 1;
        }

        STATE.match_fails = fails_save;
        STATE.match_assignments = assignments;
}

static bool
emit_match_statement(Ty *ty, Stmt const *s, bool want_result)
{
        offset_vector successes_save = STATE.match_successes;
        v00(STATE.match_successes);

        EE(s->match.e);

        bool returns = true;
        bool irrefutable = false;

        for (int i = 0; i < vN(s->match.patterns); ++i) {
                Expr *pattern = v__(s->match.patterns, i);
                Stmt *then = v__(s->match.statements, i);
                if (
                        (pattern->type == EXPRESSION_IDENTIFIER)
                     && (pattern->constraint == NULL)
                ) {
                        if (i + 1 != vN(s->match.patterns)) {
                                fail("unreachable cases in match statement");
                        }

                        irrefutable = true;

                        emit_assignment2(ty, pattern, false, true);
                        INSN(POP);

                        returns &= ES(then, want_result);
                } else {
                        returns &= emit_case(ty, pattern, NULL, then, want_result);
                }
        }

        if (!irrefutable) {
                INSN(BAD_MATCH);
        }

        patch_jumps_to(&STATE.match_successes, vN(STATE.code));
        STATE.match_successes = successes_save;

        return returns;
}

static void
emit_while_match(Ty *ty, Stmt const *s, bool want_result)
{
        begin_loop(ty, want_result, 0);

        offset_vector successes_save = STATE.match_successes;
        v00(STATE.match_successes);

        LABEL(begin);

        emit_list(ty, s->match.e);
        INSN(FIX_EXTRA);

        for (int i = 0; i < vN(s->match.patterns); ++i) {
                LOG("emitting case %d", i + 1);
                emit_case(
                        ty,
                        v__(s->match.patterns, i),
                        NULL,
                        v__(s->match.statements, i),
                        false
                );
        }

        /*
         * If nothing matches, we jump out of the loop.
         */
        INSN(CLEAR_EXTRA);
        PLACEHOLDER_JUMP(JUMP, finished);

        /*
         * Something matched, so we iterate again.
         */
        patch_jumps_to(&STATE.match_successes, vN(STATE.code));
        JUMP(begin);

        PATCH_JUMP(finished);

        if (want_result)
                INSN(NIL);

        patch_loop_jumps(ty, begin.off, vN(STATE.code));

        STATE.match_successes = successes_save;

        end_loop(ty);
}

static bool
emit_while(Ty *ty, Stmt const *s, bool want_result)
{
        begin_loop(ty, want_result, 0);

        offset_vector successes_save = STATE.match_successes;
        v00(STATE.match_successes);

        JumpGroup fails_save = STATE.match_fails;
        InitJumpGroup(&STATE.match_fails);

        LABEL(start);

        bool has_resources = false;

        bool simple = is_simple_condition(&s->iff.parts);

        for (int i = 0; i < vN(s->While.parts); ++i) {
                struct condpart *p = v__(s->While.parts, i);
                if (simple) {
                        fail_match_if_not(ty, p->e);
                } else if (p->target == NULL) {
                        INSN(SAVE_STACK_POS);
                        fail_match_if_not(ty, p->e);
                        INSN(POP_STACK_POS);
                } else {
                        if (p->target->has_resources && !has_resources) {
                                INSN(PUSH_DROP_GROUP);
                                STATE.resources += 1;
                                has_resources = true;
                        }
                        INSN(SAVE_STACK_POS);
                        emit_list(ty, p->e);
                        INSN(FIX_EXTRA);
                        emit_try_match(ty, p->target);
                        INSN(POP_STACK_POS);
                }
        }

        emit_statement(ty, s->While.block, false);

        if (has_resources) {
                INSN(DROP);
                STATE.resources -= 1;
        }

        JUMP(start);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));
        if (!simple) INSN(POP_STACK_POS);

        if (want_result) {
                INSN(NIL);
        }

        patch_loop_jumps(ty, start.off, vN(STATE.code));

        end_loop(ty);

        STATE.match_successes = successes_save;
        STATE.match_fails = fails_save;

        return false;
}

static bool
emit_if_not(Ty *ty, Stmt const *s, bool want_result)
{
        offset_vector successes_save = STATE.match_successes;
        v00(STATE.match_successes);

        JumpGroup fails_save = STATE.match_fails;
        InitJumpGroup(&STATE.match_fails);

        expression_vector assignments = STATE.match_assignments;
        v00(STATE.match_assignments);

        bool has_resources = false;

        for (int i = 0; i < vN(s->iff.parts); ++i) {
                struct condpart *p = v__(s->iff.parts, i);
                if (p->target != NULL && p->target->has_resources) {
                        has_resources = true;
                        break;
                }
        }

        if (has_resources) {
                INSN(PUSH_DROP_GROUP);
                STATE.resources += 1;
        }

        bool simple = is_simple_condition(&s->iff.parts);

        for (int i = 0; i < vN(s->iff.parts); ++i) {
                struct condpart *p = v__(s->iff.parts, i);
                if (simple) {
                        fail_match_if(ty, p->e);
                } else if (p->target == NULL) {
                        INSN(SAVE_STACK_POS);
                        fail_match_if(ty, p->e);
                        INSN(POP_STACK_POS);
                } else {
                        INSN(SAVE_STACK_POS);
                        emit_list(ty, p->e);
                        INSN(FIX_EXTRA);
                        emit_try_match(ty, p->target);
                        INSN(POP_STACK_POS);
                }
        }

        bool returns = false;

        for (int i = 0; i < vN(STATE.match_assignments); ++i) {
                Expr *e = *v_(STATE.match_assignments, i);
                emit_load(ty, e->tmp, STATE.fscope);
                emit_assignment2(ty, e->target, false, false);
                INSN(POP);
        }

        if (s->iff.otherwise != NULL) {
                returns |= emit_statement(ty, s->iff.otherwise, want_result);
        } else if (want_result) {
                INSN(NIL);
        }

        PLACEHOLDER_JUMP(JUMP, done);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));
        if (!simple) INSN(POP_STACK_POS);

        returns &= emit_statement(ty, s->iff.then, want_result);

        PATCH_JUMP(done);

        if (has_resources) {
                INSN(DROP);
                STATE.resources -= 1;
        }

        STATE.match_successes   = successes_save;
        STATE.match_fails       = fails_save;
        STATE.match_assignments = assignments;

        return returns;
}

static bool
emit_if(Ty *ty, Stmt const *s, bool want_result)
{
        offset_vector successes_save = STATE.match_successes;
        v00(STATE.match_successes);

        /* Special case for 'if not' */
        if (s->iff.neg) {
                struct condpart *p = v__(s->iff.parts, 0);

                emit_list(ty, p->e);
                INSN(FIX_EXTRA);

                bool returns = emit_case(ty, p->target, NULL, s->iff.otherwise, want_result);
                INSN(CLEAR_EXTRA);
                returns &= emit_statement(ty, s->iff.then, want_result);

                patch_jumps_to(&STATE.match_successes, vN(STATE.code));
                STATE.match_successes = successes_save;

                return returns;
        }

        JumpGroup fails_save = STATE.match_fails;
        InitJumpGroup(&STATE.match_fails);

        expression_vector assignments = STATE.match_assignments;
        v00(STATE.match_assignments);

        bool has_resources = false;

        for (int i = 0; i < vN(s->iff.parts); ++i) {
                struct condpart *p = v__(s->iff.parts, i);
                if (p->target != NULL && p->target->has_resources) {
                        has_resources = true;
                        break;
                }
        }

        if (has_resources) {
                INSN(PUSH_DROP_GROUP);
                STATE.resources += 1;
        }

        bool simple = is_simple_condition(&s->iff.parts);

        for (int i = 0; i < vN(s->iff.parts); ++i) {
                struct condpart *p = v__(s->iff.parts, i);
                if (simple) {
                        fail_match_if_not(ty, p->e);
                } else if (p->target == NULL) {
                        INSN(SAVE_STACK_POS);
                        fail_match_if_not(ty, p->e);
                        INSN(POP_STACK_POS);
                } else {
                        INSN(SAVE_STACK_POS);
                        emit_list(ty, p->e);
                        INSN(FIX_EXTRA);
                        emit_try_match(ty, p->target);
                        INSN(POP_STACK_POS);
                }
        }

        for (int i = 0; i < vN(STATE.match_assignments); ++i) {
                Expr *e = *v_(STATE.match_assignments, i);
                emit_load(ty, e->tmp, STATE.fscope);
                emit_assignment2(ty, e->target, false, false);
                INSN(POP);
        }

        bool returns = emit_statement(ty, s->iff.then, want_result);
        PLACEHOLDER_JUMP(JUMP, done);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));
        if (!simple) INSN(POP_STACK_POS);

        if (s->iff.otherwise != NULL) {
                returns &= emit_statement(ty, s->iff.otherwise, want_result);
        } else {
                if (want_result) {
                        INSN(NIL);
                }
                returns = false;
        }

        PATCH_JUMP(done);

        if (has_resources) {
                INSN(DROP);
                STATE.resources -= 1;
        }

        STATE.match_successes   = successes_save;
        STATE.match_fails       = fails_save;
        STATE.match_assignments = assignments;

        return returns;
}

static void
emit_match_expression(Ty *ty, Expr const *e)
{
        offset_vector successes_save = STATE.match_successes;
        v00(STATE.match_successes);

        EE(e->subject);

        bool irrefutable = false;

        for (int i = 0; i < vN(e->patterns); ++i) {
                Expr *pattern = v__(e->patterns, i);
                Expr *then = v__(e->thens, i);
                if (
                        (pattern->type == EXPRESSION_IDENTIFIER)
                     && (pattern->constraint == NULL)
                ) {
                        if (i + 1 != vN(e->patterns)) {
                                fail("unreachable cases in match expression");
                        }

                        irrefutable = true;

                        emit_assignment2(ty, pattern, false, true);
                        INSN(POP);

                        EE(then);
                } else {
                        emit_expression_case(ty, v__(e->patterns, i), v__(e->thens, i));
                }
        }

        if (!irrefutable) {
                INSN(BAD_MATCH);
        }

        patch_jumps_to(&STATE.match_successes, vN(STATE.code));

        STATE.match_successes = successes_save;
}

static void
emit_target(Ty *ty, Expr *target, bool def)
{
        usize start = vN(STATE.code);

        switch (target->type) {
        case EXPRESSION_RESOURCE_BINDING:
                INSN(PUSH_DROP);
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_ANY:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_TAG_PATTERN:
                annotate("%s", target->identifier);
                emit_tgt(ty, target->symbol, STATE.fscope, def);
                break;
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                EE(target->object);
                INSN(TARGET_MEMBER);
                emit_member(ty, target->member->identifier);
                break;
        case EXPRESSION_SUBSCRIPT:
                EE(target->container);
                EE(target->subscript);
                INSN(TARGET_SUBSCRIPT);
                break;
        case EXPRESSION_REF_PATTERN:
                emit_target(ty, target->target, false);
                break;
        default:
                fail("oh no!");
        }

        if (KEEP_LOCATION(target))
                add_location(ty, target, start, vN(STATE.code));
}

static void
emit_dict_compr(Ty *ty, Expr const *e)
{
        begin_loop(ty, false, 2);

        offset_vector successes_save = STATE.match_successes;
        JumpGroup fails_save = STATE.match_fails;
        v00(STATE.match_successes);
        InitJumpGroup(&STATE.match_fails);

        INSN(SAVE_STACK_POS);
        INSN(DICT);

        INSN(PUSH_INDEX);
        if (e->dcompr.pattern->type == EXPRESSION_LIST) {
                Ei32((int)vN(e->dcompr.pattern->es));
        } else {
                Ei32(1);
        }

        EE(e->dcompr.iter);

        LABEL(start);
        INSN(LOOP_ITER);
        PLACEHOLDER_JUMP(LOOP_CHECK, done);
        Ei32((int)vN(e->dcompr.pattern->es));

        add_location(ty, e, start.off, vN(STATE.code));

        for (int i = 0; i < vN(e->dcompr.pattern->es); ++i) {
                INSN(SAVE_STACK_POS);
                emit_try_match(ty, v__(e->dcompr.pattern->es, i));
                INSN(POP_STACK_POS);
                INSN(POP);
        }

        emit_statement(ty, e->compr.where, false);

        JumpPlaceholder cond_fail;
        if (e->dcompr.cond != NULL) {
                cond_fail = (PLACEHOLDER_JUMP_IF_NOT)(ty, e->dcompr.cond);
        }

        PLACEHOLDER_JUMP(JUMP, match);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));
        INSN(POP_STACK_POS);
        if (e->dcompr.cond != NULL)
                PATCH_JUMP(cond_fail);
        INSN(POP_STACK_POS);
        JUMP(start);

        PATCH_JUMP(match);
        INSN(POP_STACK_POS);

        for (int i = vN(e->keys) - 1; i >= 0; --i) {
                EE(v__(e->keys, i));
                if (v__(e->values, i) != NULL)
                        EE(v__(e->values, i));
                else
                        INSN(NIL);
        }

        INSN(DICT_COMPR);
        Ei32((int)vN(e->keys));
        JUMP(start);
        PATCH_JUMP(done);
        INSN(POP_STACK_POS);
        patch_loop_jumps(ty, start.off, vN(STATE.code));
        INSN(POP);
        INSN(POP);

        STATE.match_successes = successes_save;
        STATE.match_fails = fails_save;

        end_loop(ty);
}

static void
emit_array_range_compr(Ty *ty, Expr const *e)
{
        Expr *range = e->compr.iter;
        Expr *i = v_0(e->compr.pattern->es);

        INSN(ARRAY0);

        RangeLoop loop = BeginRangeLoop(ty, 1, false, range, i);

        ES(e->compr.where, false);

        CheckRangeLoop(ty, &loop, NULL, e->compr.cond);

        INSN(SAVE_STACK_POS);

        for (int i = vN(e->elements) - 1; i >= 0; --i) {
                if (v__(e->aconds, i) != NULL) {
                        PLACEHOLDER_JUMP_IF_NOT(v__(e->aconds, i), skip);
                        EE(v__(e->elements, i));
                        PATCH_JUMP(skip);
                } else {
                        EE(v__(e->elements, i));
                }
        }

        INSN(ARRAY_COMPR);

        EndRangeLoop(ty, &loop);
}

static void
emit_array_compr(Ty *ty, Expr const *e)
{
        begin_loop(ty, false, 2);

        offset_vector successes_save = STATE.match_successes;
        JumpGroup fails_save = STATE.match_fails;
        v00(STATE.match_successes);
        InitJumpGroup(&STATE.match_fails);

        INSN(ARRAY0);

        INSN(PUSH_INDEX);
        if (e->compr.pattern->type == EXPRESSION_LIST) {
                Ei32((int)vN(e->compr.pattern->es));
        } else {
                Ei32(1);
        }

        EE(e->compr.iter);

        LABEL(start);
        INSN(LOOP_ITER);
        PLACEHOLDER_JUMP(LOOP_CHECK, done);
        Ei32((int)vN(e->compr.pattern->es));

        add_location(ty, e, start.off, vN(STATE.code));

        for (int i = 0; i < vN(e->compr.pattern->es); ++i) {
                INSN(SAVE_STACK_POS);
                emit_try_match(ty, v__(e->compr.pattern->es, i));
                INSN(POP_STACK_POS_POP);
        }

        emit_statement(ty, e->compr.where, false);

        JumpPlaceholder cond_fail;
        if (e->compr.cond != NULL) {
                cond_fail = (PLACEHOLDER_JUMP_IF_NOT)(ty, e->compr.cond);
        }

        PLACEHOLDER_JUMP(JUMP, match);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));
        INSN(POP_STACK_POS);
        if (e->compr.cond != NULL)
                PATCH_JUMP(cond_fail);
        INSN(POP_STACK_POS);
        JUMP(start);

        PATCH_JUMP(match);
        INSN(POP_STACK_POS);

        INSN(SAVE_STACK_POS);

        for (int i = vN(e->elements) - 1; i >= 0; --i) {
                if (v__(e->aconds, i) != NULL) {
                        PLACEHOLDER_JUMP_IF_NOT(v__(e->aconds, i), skip);
                        EE(v__(e->elements, i));
                        PATCH_JUMP(skip);
                } else {
                        EE(v__(e->elements, i));
                }
        }

        INSN(ARRAY_COMPR);
        JUMP(start);
        PATCH_JUMP(done);
        INSN(POP_STACK_POS);
        patch_loop_jumps(ty, start.off, vN(STATE.code));
        INSN(POP);
        INSN(POP);

        STATE.match_successes = successes_save;
        STATE.match_fails     = fails_save;

        end_loop(ty);
}

static void
emit_spread(Ty *ty, Expr const *e, bool nils)
{
        INSN(PUSH_INDEX);
        Ei32(1);

        if (e != NULL) {
                EE(e);
        } else {
                INSN(SWAP);
        }

        LABEL(start);
        INSN(LOOP_ITER);

        PLACEHOLDER_JUMP(SPREAD_CHECK, done);
        Eu8(nils);

        JUMP(start);

        PATCH_JUMP(done);

        INSN(POP_STACK_POS_POP);
        INSN(POP);
}

static void
emit_spread_tuple(Ty *ty, Expr const *e)
{
        INSN(SAVE_STACK_POS);

        EE(e);

        PLACEHOLDER_JUMP(JUMP_IF_TYPE, skip);
        Ei32(VALUE_TUPLE);
        emit_spread(ty, NULL, false);
        INSN(GATHER_TUPLE);
        PLACEHOLDER_JUMP(JUMP, end);

        PATCH_JUMP(skip);
        INSN(DROP_STACK_POS);

        PATCH_JUMP(end);
}

static void
emit_conditional(Ty *ty, Expr const *e)
{
        PLACEHOLDER_JUMP_IF_NOT(e->cond, otherwise);
        EE(e->then);
        PLACEHOLDER_JUMP(JUMP, end);
        PATCH_JUMP(otherwise);
        EE(e->otherwise);
        PATCH_JUMP(end);
}

static RangeLoop
BeginRangeLoop(
        Ty *ty,
        i32 n,
        bool want_result,
        Expr *range,
        Expr *target
)
{
        bool reverse;
        bool inclusive;

        if (range->type == EXPRESSION_MEMBER_ACCESS) {
                range = range->object;
                reverse = true;
        } else {
                reverse = false;
        }

        inclusive = (range->type == EXPRESSION_DOT_DOT_DOT);

        Expr *start = !reverse ? range->left  : range->right;
        Expr *stop  = !reverse ? range->right : range->left;

        Expr zero = { .type = EXPRESSION_INTEGER, .integer = 0          };
        Expr inf  = { .type = EXPRESSION_INTEGER, .integer = INTMAX_MAX };

        if (start == NULL) start = &zero;
        if (stop  == NULL) stop  = (reverse ? &zero : &inf);

        EE(stop);
        EE(start);

        if (reverse && !inclusive) {
                INSN(DEC);
        }

        LABEL(begin);

        INSN(DUP2);
        INSN(SWAP);

        JumpPlaceholder end;

        switch ((reverse << 1) | inclusive) {
        case 0: end = (PLACEHOLDER_JUMP)(ty, INSTR_JGE); break;
        case 1: end = (PLACEHOLDER_JUMP)(ty, INSTR_JGT); break;
        case 2:
        case 3: end = (PLACEHOLDER_JUMP)(ty, INSTR_JLT); break;
        }

        begin_loop(ty, want_result, 2 + n);

        emit_assignment2(ty, target, false, true);

        return (RangeLoop) {
                .start     = start,
                .stop      = stop,
                .begin     = begin,
                .end       = end,
                .inclusive = inclusive,
                .reverse   = reverse
        };
}

static void
CheckRangeLoop(
        Ty *ty,
        RangeLoop *loop,
        Expr *_while,
        Expr *_if
)
{
        if (_while != NULL) {
                loop->_while = _while;
                loop->exit = (PLACEHOLDER_JUMP_IF_NOT)(ty, _while);
        }

        if (_if != NULL) {
                loop->_if = _if;
                loop->skip = (PLACEHOLDER_JUMP_IF_NOT)(ty, _if);
        }
}

static void
EndRangeLoop(Ty *ty, RangeLoop *loop)
{
        if (loop->_if != NULL) {
                PATCH_JUMP(loop->skip);
        }

        LABEL(next);
        loop->next = next;

        INSNx(!loop->reverse ? INSTR_INC : INSTR_DEC);

        JUMP(loop->begin);

        if (loop->_while != NULL) {
                PATCH_JUMP(loop->exit);
        }

        PATCH_JUMP(loop->end);

        INSN(POP);
        INSN(POP);

        if (get_loop(ty, 0)->wr) {
                INSN(NIL);
        }

        patch_loop_jumps(ty, loop->next.off, vN(STATE.code));

        end_loop(ty);
}

static void
emit_range_loop(Ty *ty, Stmt const *s, bool want_result)
{
        Expr *range = s->each.array;
        Expr *i = v_0(s->each.target->es);

        RangeLoop loop = BeginRangeLoop(ty, 0, want_result, range, i);
        CheckRangeLoop(ty, &loop, s->each.stop, s->each.cond);
        ES(s->each.body, false);
        EndRangeLoop(ty, &loop);
}

static void
emit_for_each(Ty *ty, Stmt const *s, bool want_result)
{
        begin_loop(ty, want_result, 2);

        offset_vector successes_save = STATE.match_successes;
        JumpGroup         fails_save = STATE.match_fails;

        v00(STATE.match_successes);
        InitJumpGroup(&STATE.match_fails);

        INSN(PUSH_INDEX);
        Ei32((int)vN(s->each.target->es));

        EE(s->each.array);

        LABEL(start);
        INSN(LOOP_ITER);

#ifndef TY_PROFILER
        add_location(ty, s->each.array, start.off, vN(STATE.code));
#endif

        PLACEHOLDER_JUMP(LOOP_CHECK, done);

        Ei32((int)vN(s->each.target->es));

        if (s->each.target->has_resources) {
                INSN(PUSH_DROP_GROUP);
                STATE.resources += 1;
        }

        for (int i = 0; i < vN(s->each.target->es); ++i) {
                INSN(SAVE_STACK_POS);
                emit_try_match(ty, v__(s->each.target->es, i));
                INSN(POP_STACK_POS);
                INSN(POP);
        }

        JumpPlaceholder should_stop;
        if (s->each.stop != NULL) {
                should_stop = (PLACEHOLDER_JUMP_IF_NOT)(ty, s->each.stop);
        }

        PLACEHOLDER_JUMP(JUMP, match);

        EMIT_GROUP_LABEL(STATE.match_fails, ":Fail");
        patch_jumps_to(&STATE.match_fails, vN(STATE.code));

        // for Some(i) in [None] { ... }
        add_location(ty, s->each.target, vN(STATE.code), vN(STATE.code) + 2);
        INSN(POP_STACK_POS);
        INSN(BAD_MATCH);

        PATCH_JUMP(match);

        INSN(POP_STACK_POS);

        if (s->each.cond != NULL) {
                EE(s->each.cond);
                JUMP_IF_NOT(start);
        }

        emit_statement(ty, s->each.body, false);

        if (s->each.target->has_resources) {
                INSN(DROP);
                STATE.resources -= 1;
        }

        JUMP(start);

        if (s->each.stop != NULL)
                PATCH_JUMP(should_stop);

        PATCH_JUMP(done);

        INSN(POP_STACK_POS);
        INSN(POP);
        INSN(POP);

        if (want_result)
                INSN(NIL);

        patch_loop_jumps(ty, start.off, vN(STATE.code));

        STATE.match_successes = successes_save;
        STATE.match_fails     = fails_save;

        end_loop(ty);
}

static bool
check_multi(Expr *target, Expr const *e, int *n)
{
        if (is_call(e))
                return true;

        if (e->type != EXPRESSION_LIST)
                return (*n = 1), false;

        for (*n = 0; *n < vN(e->es); ++*n) {
                if (
                        is_call(v__(e->es, *n))
                     || (v__(e->es, *n)->type == EXPRESSION_SPREAD)
                ) {
                        return true;
                }
        }

        return *n == vN(target->es);
}

static void
emit_assignment2(Ty *ty, Expr *target, bool maybe, bool def)
{
        char instr = maybe ? INSTR_MAYBE_ASSIGN : INSTR_ASSIGN;

        usize start = vN(STATE.code);

        bool after = false;

        switch (target->type) {
        case EXPRESSION_ARRAY:
                for (int i = 0; i < vN(target->elements); ++i) {
                        if (v__(target->elements, i)->type == EXPRESSION_MATCH_REST) {
                                if (after) {
                                        PushContext(ty, v__(target->elements, i));
                                        fail("array pattern cannot contain multiple gather elements");
                                } else {
                                        after = true;
                                }
                                emit_target(ty, v__(target->elements, i), def);
                                PLACEHOLDER_JUMP(ARRAY_REST, bad);
                                Ei32(i);
                                Ei32(vN(target->elements) - i - 1);
                                INSN(JUMP);
                                Ei32(1);
                                PATCH_JUMP(bad);
                                INSN(BAD_MATCH);
                        } else {
                                INSN(PUSH_ARRAY_ELEM);
                                if (after) {
                                        if (v__(target->optional, i)) {
                                                PushContext(ty, v__(target->elements, i));
                                                fail("optional element cannot come after a gather element in array pattern");
                                        }
                                        Ei32(i - vN(target->elements));
                                } else {
                                        Ei32(i);
                                }
                                Eu1(!v__(target->optional, i));
                                emit_assignment2(ty, v__(target->elements, i), maybe, def);
                                INSN(POP);
                        }
                }
                break;
        case EXPRESSION_DICT:
                for (int i = 0; i < vN(target->keys); ++i) {
                        INSN(DUP);
                        EE(v__(target->keys, i));
                        INSN(SUBSCRIPT);
                        emit_assignment2(ty, v__(target->values, i), maybe, def);
                        INSN(POP);
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                INSN(UNTAG_OR_DIE);
                Ei32(tag_app_tag(target));
                emit_assignment2(ty, target->tagged, maybe, def);
                break;
        case EXPRESSION_TAG_PATTERN:
                emit_target(ty, target, def);
                INSN(STEAL_TAG);
                emit_assignment2(ty, target->tagged, maybe, def);
                break;
        case EXPRESSION_VIEW_PATTERN:
                INSN(DUP);
                EE(target->left);
                INSN(CALL);
                Ei32(1);
                Ei32(0);
                add_location(ty, target->left, start, vN(STATE.code));
                emit_assignment2(ty, target->right, maybe, def);
                INSN(POP);
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                INSN(DUP);
                EE(target->left);
                INSN(CALL);
                Ei32(1);
                Ei32(0);
                add_location(ty, target->left, start, vN(STATE.code));
                INSN(THROW_IF_NIL);
                add_location(ty, target, vN(STATE.code) - 1, vN(STATE.code));
                emit_assignment2(ty, target->right, maybe, def);
                INSN(POP);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                INSN(THROW_IF_NIL);
                emit_target(ty, target, def);
                (emit_instr)(ty, instr);
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < vN(target->es); ++i) {
                        if (v__(target->es, i)->type == EXPRESSION_MATCH_REST) {
                                if (has_any_names(target)) {
                                        emit_record_rest(ty, target, i, true);
                                } else {
                                        // FIXME: should we handle elements after the match-rest?
                                        emit_target(ty, v__(target->es, i), def);
                                        INSN(TUPLE_REST);
                                        Ei32(2 * sizeof (int) + 1);
                                        Ei32(i);
                                        INSN(JUMP);
                                        Ei32(1);
                                        INSN(BAD_MATCH);
                                }
                        } else if (v__(target->names, i) != NULL) {
                                INSN(PUSH_TUPLE_MEMBER);
                                Eu1(v__(target->required, i));
                                Ei32(M_ID(v__(target->names, i)));
                                emit_assignment2(ty, v__(target->es, i), maybe, def);
                                INSN(POP);
                        } else {
                                INSN(PUSH_TUPLE_ELEM);
                                Ei32(i);
                                emit_assignment2(ty, v__(target->es, i), maybe, def);
                                INSN(POP);
                        }
                }
                break;
        default:
                emit_target(ty, target, def);
                INSNx(instr);
                if (
                        (target->type == EXPRESSION_IDENTIFIER)
                     && (target->constraint != NULL)
                     && RUNTIME_CONSTRAINTS
                ) {
                        usize start = vN(STATE.code);
                        INSN(DUP);
                        EA(target->constraint);
                        PLACEHOLDER_JUMP(JUMP_IF, good);
                        INSN(BAD_ASSIGN);
                        emit_string(ty, target->identifier);
                        PATCH_JUMP(good);
                        add_location(ty, target->constraint, start, vN(STATE.code));
                }

#ifndef TY_PROFILER
                // Don't need location info, can't fail here
                return;
#endif
        }

        add_location(ty, target, start, vN(STATE.code));
}

static void
emit_assignment(Ty *ty, Expr *target, Expr const *e, bool maybe, bool def)
{
        if (target->has_resources) {
                INSN(PUSH_DROP_GROUP);
                STATE.resources += 1;
        }

        if (target->type == EXPRESSION_LIST) {
                emit_list(ty, e);
                INSN(FIX_TO);
                Ei32(vN(target->es));
                for (int i = 0; i < vN(target->es); ++i) {
                        emit_assignment2(ty, v__(target->es, i), maybe, def);
                        INSN(POP);
                }
                INSN(POP);
                INSN(NIL);
        } else {
                EE(e);
                emit_assignment2(ty, target, maybe, def);
        }
}

static void
emit_non_nil_expr(Ty *ty, Expr const *e, bool none)
{
        EE(e);
        INSN(DUP);

        PLACEHOLDER_JUMP(JUMP_IF_NIL, skip);
        PLACEHOLDER_JUMP(JUMP, good);
        PATCH_JUMP(skip);

        INSN(POP);

        if (none) {
                INSN(NONE);
        }

        PATCH_JUMP(good);
}

static void
EmitMethodCall(
        Ty *ty,
        Expr const *object,
        Expr const *method,
        bool dyn,
        expression_vector const *args,
        expression_vector const *conds,
        StringVector const *kws,
        expression_vector const *kwargs,
        expression_vector const *kwconds,
        bool strict
)
{
        bool variadic = any_variadic(vv(*args), vv(*conds), vN(*args));

        if (variadic) {
                INSN(SAVE_STACK_POS);
        }

        for (usize i = 0; i < vN(*args); ++i) {
                if (v__(*args, i) == NULL) {
                        continue;
                } else if (v__(*conds, i) != NULL) {
                        PLACEHOLDER_JUMP_IF_NOT(v__(*conds, i), skip);
                        EE(v__(*args, i));
                        PATCH_JUMP(skip);
                } else {
                        EE(v__(*args, i));
                }
        }

        for (usize i = 0; i < vN(*kwargs); ++i) {
                EE(v__(*kwargs, i));
        }

        if (object != NULL) {
                EE(object);
        }

        if (dyn) {
                EE(method);
        }

        if (object == NULL) {
                INSN(CALL_SELF_METHOD);
        } else if (!strict) {
                INSN(TRY_CALL_METHOD);
        } else {
                INSN(CALL_METHOD);
        }

        if (variadic) {
                Ei32(-1);
        } else {
                Ei32(vN(*args));
        }

        if (dyn) {
                Ei32(-1);
        } else {
                emit_member(ty, method->identifier);
        }

        Ei32(vN(*kwargs));

        for (usize i = vN(*kwargs); i > 0; --i) {
                emit_string(ty, v__(*kws, i - 1));
        }
}

static void
EmitFunctionCall(Ty *ty, Expr const *e)
{
        if (is_variadic(e)) {
                INSN(SAVE_STACK_POS);
        }

        for (usize i = 0; i < vN(e->args); ++i) {
                if (is_placeholder(v__(e->args, i))) {
                        continue;
                } else if (v__(e->fconds, i) != NULL) {
                        PLACEHOLDER_JUMP_IF_NOT(v__(e->fconds, i), skip);
                        EE(v__(e->args, i));
                        PATCH_JUMP(skip);
                } else {
                        EE(v__(e->args, i));
                }
        }

        for (usize i = 0; i < vN(e->kwargs); ++i) {
                if (v__(e->fkwconds, i) == NULL) {
                        EE(v__(e->kwargs, i));
                } else {
                        EE(v__(e->fkwconds, i));
                        PLACEHOLDER_JUMP(NONE_IF_NOT, skip);
                        EE(v__(e->kwargs, i));
                        PATCH_JUMP(skip);
                }
        }

        EE(e->function);
        INSN(CALL);

        if (is_variadic(e)) {
                Ei32(-1);
        } else {
                Ei32(vN(e->args));
        }

        Ei32(vN(e->kwargs));
        for (usize i = vN(e->kws); i > 0; --i) {
                emit_string(ty, v__(e->kws, i - 1));
        }
}

static bool
emit_expr(Ty *ty, Expr const *e, bool need_loc)
{
        STATE.start = e->start;
        STATE.end   = e->end;

        usize start = vN(STATE.code);
        void    *ctx = PushContext(ty, e);

        bool returns = false;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                // FIXME
                if (false) {
                        fail("%s%s%s is uninitialized here", TERM(93), e->identifier, TERM(0));
                }
                emit_load(ty, e->symbol, STATE.fscope);
                break;

        case EXPRESSION_OPERATOR:
                INSN(OPERATOR);
                Ei32(e->op.u);
                Ei32(e->op.b);
                break;

        case EXPRESSION_IFDEF:
                emit_load(ty, e->symbol, STATE.fscope);
                INSN(TAG_PUSH);
                Ei32(TAG_SOME);
                break;

        case EXPRESSION_TYPE_OF:
                INSN(TYPE);
                emit_symbol((uptr)e->operand->_type);
                break;

        case EXPRESSION_TYPE:
                INSN(TYPE);
                emit_symbol((uptr)e->_type);
                break;

        case EXPRESSION_NONE:
                INSN(TAG);
                Ei32(TAG_NONE);
                break;

        case EXPRESSION_VALUE:
                INSN(VALUE);
                emit_symbol((uptr)e->v);
                break;

        case EXPRESSION_SUPER:
                emit_super(ty, e);
                break;

        case EXPRESSION_MATCH:
                emit_match_expression(ty, e);
                break;

        case EXPRESSION_TAG_APPLICATION:
                EE(e->tagged);
                INSN(TAG_PUSH);
                Ei32(tag_app_tag(e));
                break;

        case EXPRESSION_DOT_DOT:
                EE(e->left);
                if (e->right != NULL) {
                        EE(e->right);
                        INSN(RANGE);
                } else {
                        INSN(CALL_METHOD);
                        Ei32(0);
                        Ei32(vN(NAMES));
                        Ei32(0);
                }
                break;

        case EXPRESSION_DOT_DOT_DOT:
                EE(e->left);
                EE(e->right);
                INSN(INCRANGE);
                break;

        case EXPRESSION_EQ:
                emit_assignment(ty, e->target, e->value, false, false);
                break;

        case EXPRESSION_MAYBE_EQ:
                emit_assignment(ty, e->target, e->value, true, false);
                break;

        case EXPRESSION_INTEGER:
                INSN(INTEGER);
                emit_integer(ty, e->integer);
                break;

        case EXPRESSION_BOOLEAN:
                INSN(BOOLEAN);
                Eu1(e->boolean);
                break;

        case EXPRESSION_REAL:
                INSN(REAL);
                emit_float(ty, e->real);
                break;

        case EXPRESSION_STRING:
                INSN(STRING);
                emit_string(ty, e->string);
                break;

        case EXPRESSION_SPECIAL_STRING:
                if (e->lang != NULL) {
                        emit_lang_string(ty, e);
                } else {
                        emit_special_string(ty, e);
                }
                break;

        case EXPRESSION_EVAL:
                EE(e->operand);
                INSN(EVAL);
                emit_symbol((uptr)e->escope);
                break;

        case EXPRESSION_TRACE:
                INSN(TRACE);
                break;

        case EXPRESSION_TAG:
                INSN(TAG);
                Ei32(e->symbol->tag);
                break;

        case EXPRESSION_REGEX:
                INSN(REGEX);
                emit_symbol((uptr)e->regex);
                break;

        case EXPRESSION_ARRAY:
                if (vN(e->elements) == 0) {
                        INSN(ARRAY0);
                } else {
                        INSN(SAVE_STACK_POS);
                        for (int i = 0; i < vN(e->elements); ++i) {
                                if (v__(e->aconds, i) != NULL) {
                                        PLACEHOLDER_JUMP_IF_NOT(v__(e->aconds, i), skip);
                                        if (v__(e->optional, i)) {
                                                emit_non_nil_expr(ty, v__(e->elements, i), false);
                                        } else {
                                                EE(v__(e->elements, i));
                                        }
                                        PATCH_JUMP(skip);
                                } else if (v__(e->optional, i)) {
                                        emit_non_nil_expr(ty, v__(e->elements, i), false);
                                } else {
                                        EE(v__(e->elements, i));
                                }
                        }
                        INSN(ARRAY);
                }
                break;

        case EXPRESSION_ARRAY_COMPR:
                if (IsSimpleRange(e->compr.iter)) {
                        emit_array_range_compr(ty, e);
                } else {
                        emit_array_compr(ty, e);
                }
                break;

        case EXPRESSION_DICT:
                INSN(SAVE_STACK_POS);
                for (int i = vN(e->keys) - 1; i >= 0; --i) {
                        if (v__(e->keys, i)->type == EXPRESSION_SPREAD) {
                                emit_spread(ty, v__(e->keys, i)->value, true);
                        } else {
                                EE(v__(e->keys, i));
                                if (v__(e->keys, i)->type == EXPRESSION_SPLAT) {
                                        INSN(NONE);
                                } else if (v__(e->values, i) == NULL) {
                                        INSN(NIL);
                                } else {
                                        EE(v__(e->values, i));
                                }
                        }
                }
                INSN(DICT);
                if (e->dflt != NULL) {
                        EE(e->dflt);
                        INSN(DICT_DEFAULT);
                }
                break;

        case EXPRESSION_DICT_COMPR:
                emit_dict_compr(ty, e);
                break;

        case EXPRESSION_NIL:
                INSN(NIL);
                break;

        case EXPRESSION_SELF:
                INSN(NIL);
                break;

        case EXPRESSION_SPLAT:
                EE(e->value);
                break;

        case EXPRESSION_DYN_MEMBER_ACCESS:
                EE(e->object);
                EE(e->member);
                if (e->maybe)
                        INSN(TRY_GET_MEMBER);
                else
                        INSN(GET_MEMBER);
                break;

        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                EE(e->object);
                if (e->maybe)
                        INSN(TRY_MEMBER_ACCESS);
                else
                        INSN(MEMBER_ACCESS);
                emit_member(ty, e->member->identifier);
                break;

        case EXPRESSION_SUBSCRIPT:
                if (e->subscript->type == EXPRESSION_LIST) {
                        if (vN(e->subscript->es) > 1) {
                                for (int i = 0; i < vN(e->subscript->es); ++i) {
                                        EE(v__(e->subscript->es, i));
                                }
                                EE(e->container);
                                INSN(CALL_METHOD);
                                Ei32(vN(e->subscript->es));
                                Ei32(NAMES.subscript);
                                Ei32(0);
                        } else {
                                EE(v__(e->container->es, 0));
                                EE(e->subscript);
                                INSN(SUBSCRIPT);
                        }
                } else {
                        EE(e->container);
                        EE(e->subscript);
                        INSN(SUBSCRIPT);
                }
                break;

        case EXPRESSION_SLICE:
                if (e->slice.i != NULL) EE(e->slice.i);
                else                    INSN(NIL);
                if (e->slice.j != NULL) EE(e->slice.j);
                else                    INSN(NIL);
                if (e->slice.k != NULL) EE(e->slice.k);
                else                    INSN(NIL);
                EE(e->slice.e);
                INSN(SLICE);
                break;

        case EXPRESSION_STATEMENT:
                returns |= emit_statement(ty, e->statement, true);
                break;

        case EXPRESSION_FUNCTION_CALL:
                if (IsLocalMember(ty, e->function, STATE.fscope)) {
                        EmitMethodCall(
                                ty,
                                NULL,
                                e->function,
                                false,
                                &e->args,
                                &e->fconds,
                                &e->kws,
                                &e->kwargs,
                                &e->fkwconds,
                                true
                        );
                } else {
                        EmitFunctionCall(ty, e);
                }
                break;

        case EXPRESSION_METHOD_CALL:
                EmitMethodCall(
                        ty,
                        e->object,
                        e->method,
                        false,
                        &e->method_args,
                        &e->mconds,
                        &e->method_kws,
                        &e->method_kwargs,
                        NULL,
                        !e->maybe
                );
                break;

        case EXPRESSION_DYN_METHOD_CALL:
                EmitMethodCall(
                        ty,
                        e->object,
                        e->method,
                        true,
                        &e->method_args,
                        &e->mconds,
                        &e->method_kws,
                        &e->method_kwargs,
                        NULL,
                        !e->maybe
                );
                break;

        case EXPRESSION_WITH:
                emit_with(ty, e);
                break;

        case EXPRESSION_YIELD:
                emit_yield(ty, (Expr const **)vv(e->es), vN(e->es), true);
                break;

        case EXPRESSION_THROW:
                //if (try != NULL && try->finally) {
                //        fail("invalid 'throw' statement (occurs in a finally block)");
                //}
                EE(e->throw);
                INSN(THROW);
                break;

        case EXPRESSION_SPREAD:
                emit_spread(ty, e->value, false);
                break;

        case EXPRESSION_UNARY_OP:
                EE(e->operand);
                INSN(UNARY_OP);
                Ei32(intern(&xD.members, e->uop)->id);
                break;

        case EXPRESSION_USER_OP:
                EE(e->left);
                EE(e->right);
                INSN(BINARY_OP);
                Ei32(intern(&xD.b_ops, e->op_name)->id);
                break;

        case EXPRESSION_BIT_OR:
                EE(e->left);
                EE(e->right);
                INSN(BIT_OR);
                break;

        case EXPRESSION_BIT_AND:
                EE(e->left);
                EE(e->right);
                INSN(BIT_AND);
                break;

        case EXPRESSION_TYPE_UNION:
                for (int i = 0; i < vN(e->es); ++i) {
                        EE(v__(e->es, i));
                        if (i > 0) {
                                INSN(BIT_OR);
                        }
                }
                break;

        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
                EE(e->left);
                EE(e->right);
                INSN(CALL_METHOD);
                Ei32(1);
                Ei32(NAMES.contains);
                Ei32(0);
                if (e->type == EXPRESSION_NOT_IN) {
                        INSN(NOT);
                }
                break;

        case EXPRESSION_GENERATOR:
                emit_function(ty, e);
                INSN(CALL);
                Ei32(0);
                Ei32(0);
                break;

        case EXPRESSION_FUNCTION:
        case EXPRESSION_MULTI_FUNCTION:
                WITH_SELF(e->self) {
                        emit_function(ty, e);
                }
                break;

        case EXPRESSION_PLUS:
                EE(e->left);
                EE(e->right);
                INSN(ADD);
                break;

        case EXPRESSION_MINUS:
                EE(e->left);
                EE(e->right);
                INSN(SUB);
                break;

        case EXPRESSION_STAR:
                EE(e->left);
                EE(e->right);
                INSN(MUL);
                break;

        case EXPRESSION_DIV:
                EE(e->left);
                EE(e->right);
                INSN(DIV);
                break;

        case EXPRESSION_SHL:
                EE(e->left);
                EE(e->right);
                INSN(SHL);
                break;

        case EXPRESSION_SHR:
                EE(e->left);
                EE(e->right);
                INSN(SHR);
                break;

        case EXPRESSION_XOR:
                EE(e->left);
                EE(e->right);
                INSN(BIT_XOR);
                break;

        case EXPRESSION_PERCENT:
                EE(e->left);
                EE(e->right);
                INSN(MOD);
                break;

        case EXPRESSION_AND:
                emit_and(ty, e->left, e->right);
                break;

        case EXPRESSION_OR:
                emit_or(ty, e->left, e->right);
                break;

        case EXPRESSION_WTF:
                emit_coalesce(ty, e->left, e->right);
                break;

        case EXPRESSION_CONDITIONAL:
                emit_conditional(ty, e);
                break;

        case EXPRESSION_LT:
                EE(e->left);
                EE(e->right);
                INSN(LT);
                break;

        case EXPRESSION_LEQ:
                EE(e->left);
                EE(e->right);
                INSN(LEQ);
                break;

        case EXPRESSION_GT:
                EE(e->left);
                EE(e->right);
                INSN(GT);
                break;

        case EXPRESSION_GEQ:
                EE(e->left);
                EE(e->right);
                INSN(GEQ);
                break;

        case EXPRESSION_CMP:
                EE(e->left);
                EE(e->right);
                INSN(CMP);
                break;

        case EXPRESSION_DBL_EQ:
                EE(e->left);
                EE(e->right);
                INSN(EQ);
                break;

        case EXPRESSION_NOT_EQ:
                EE(e->left);
                EE(e->right);
                INSN(NEQ);
                break;

        case EXPRESSION_CHECK_MATCH:
                EE(e->left);
                EE(e->right);
                INSN(CHECK_MATCH);
                break;

        case EXPRESSION_PREFIX_BANG:
                EE(e->operand);
                INSN(NOT);
                break;

        case EXPRESSION_PREFIX_HASH:
                EE(e->operand);
                INSN(COUNT);
                break;

        case EXPRESSION_ENTER:
                EE(e->operand);
                INSN(ENTER);
                break;

        case EXPRESSION_PREFIX_QUESTION:
                EE(e->operand);
                INSN(QUESTION);
                break;

        case EXPRESSION_PREFIX_AT:
                EE(e->operand);
                INSN(GET_TAG);
                break;

        case EXPRESSION_PREFIX_MINUS:
                EE(e->operand);
                INSN(NEG);
                break;

        case EXPRESSION_PREFIX_INC:
                emit_target(ty, e->operand, false);
                INSN(PRE_INC);
                break;

        case EXPRESSION_PREFIX_DEC:
                emit_target(ty, e->operand, false);
                INSN(PRE_DEC);
                break;

        case EXPRESSION_POSTFIX_INC:
                emit_target(ty, e->operand, false);
                INSN(POST_INC);
                break;

        case EXPRESSION_POSTFIX_DEC:
                emit_target(ty, e->operand, false);
                INSN(POST_DEC);
                break;

        case EXPRESSION_PLUS_EQ:
                EE(e->value);
                emit_target(ty, e->target, false);
                INSN(MUT_ADD);
                break;

        case EXPRESSION_STAR_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_MUL);
                break;

        case EXPRESSION_DIV_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_DIV);
                break;

        case EXPRESSION_MOD_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_MOD);
                break;

        case EXPRESSION_MINUS_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_SUB);
                break;

        case EXPRESSION_AND_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_AND);
                break;

        case EXPRESSION_OR_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_OR);
                break;

        case EXPRESSION_XOR_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_XOR);
                break;

        case EXPRESSION_SHR_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_SHR);
                break;

        case EXPRESSION_SHL_EQ:
                emit_target(ty, e->target, false);
                EE(e->value);
                INSN(MUT_SHL);
                break;

        case EXPRESSION_TUPLE:
                for (int i = 0; i < vN(e->es); ++i) {
                        if (v__(e->tconds, i) != NULL) {
                                EE(v__(e->tconds, i));
                                PLACEHOLDER_JUMP(JUMP_IF_NOT, skip);
                                if (!v__(e->required, i)) {
                                        emit_non_nil_expr(ty, v__(e->es, i), true);
                                } else {
                                        EE(v__(e->es, i));
                                }
                                PLACEHOLDER_JUMP(JUMP, good);
                                PATCH_JUMP(skip);
                                INSN(NONE);
                                PATCH_JUMP(good);
                        } else if (!v__(e->required, i)) {
                                emit_non_nil_expr(ty, v__(e->es, i), true);
                        } else if (v__(e->es, i)->type == EXPRESSION_SPREAD) {
                                emit_spread_tuple(ty, v__(e->es, i)->value);
                        } else {
                                EE(v__(e->es, i));
                        }
                }
                INSN(TUPLE);
                Ei32(vN(e->es));
                for (int i = 0; i < vN(e->names); ++i) {
                        if (v__(e->names, i) != NULL) {
                                if (strcmp(v__(e->names, i), "*") == 0) {
                                        Ei32(-2);
                                } else {
                                        Ei32(M_ID(v__(e->names, i)));
                                }
                        } else {
                                Ei32(-1);
                        }
                }
                break;

        case EXPRESSION_TUPLE_SPEC:
                INSN(SAVE_STACK_POS);
                for (int i = 0; i < vN(e->es); ++i) {
                        if (v__(e->names, i) == NULL) {
                                INSN(NIL);
                        } else {
                                INSN(STRING);
                                emit_string(ty, v__(e->names, i));
                        }
                        EE(v__(e->es, i));
                        INSN(BOOLEAN);
                        Eu8(v__(e->required, i));
                        INSN(TUPLE);
                        Ei32(3);
                        Ei32(-1);
                        Ei32(-1);
                        Ei32(-1);
                }
                INSN(ARRAY);
                INSN(CLASS);
                Ei32(CLASS_TUPLE_SPEC);
                INSN(CALL);
                Ei32(1);
                Ei32(0);
                break;



        case EXPRESSION_TEMPLATE:
                for (int i = vN(e->template.holes) - 1; i >= 0; --i) {
                        EE(v__(e->template.holes, i));
                }
                INSN(RENDER_TEMPLATE);
                emit_symbol((uptr)e);
                break;

        case EXPRESSION_NAMESPACE:
                INSN(NAMESPACE);
                emit_symbol(e);
                break;

        case EXPRESSION_FUNCTION_TYPE:
                INSN(BOOLEAN);
                Eu1(true);
                break;

        case EXPRESSION_CAST:
                EE(e->left);
                break;

        case EXPRESSION_MATCH_ANY:
                INSN(BOOLEAN);
                Eu1(true);
                break;

        case EXPRESSION_LIST:
                if (vN(e->es) > 0) {
                        EE(v__(e->es, 0));
                        break;
                }
                // v v v v v v v v v v v v v v

        default:
                fail("expression unexpected in this context: %s", ExpressionTypeName(e));
        }

        if (KEEP_LOCATION(e) || need_loc)
                add_location(ty, e, start, vN(STATE.code));

        RestoreContext(ty, ctx);

        return returns;
}

static bool
emit_expression(Ty *ty, Expr const *e)
{
        bool will_return;

        if (e->type > EXPRESSION_MAX_TYPE) {
                will_return = emit_statement(ty, (Stmt *)e, true);
        } else {
                will_return = emit_expr(ty, e, false);
        }

        return will_return;
}

static bool
emit_statement(Ty *ty, Stmt const *s, bool want_result)
{
        if (s == NULL) {
                static Stmt null = { .type = STATEMENT_NULL };
                s = &null;
        }

        STATE.start = s->start;
        STATE.end = s->end;

        bool returns = false;

        int resources = STATE.resources;
        usize start = vN(STATE.code);
        LoopState *loop = get_loop(ty, 0);
        void *ctx = PushContext(ty, s);

        switch (s->type) {
        case STATEMENT_BLOCK:
        case STATEMENT_MULTI:
                for (int i = 0; !returns && i < vN(s->statements); ++i) {
                        bool wr = want_result && (i + 1 == vN(s->statements));
                        returns |= emit_statement(ty, v__(s->statements, i), wr);
                }
                if (vN(s->statements) > 0) {
                        want_result = false;
                }
                while (STATE.resources > resources) {
                        INSN(DROP);
                        STATE.resources -= 1;
                }
                break;

        case STATEMENT_MATCH:
                returns |= emit_match_statement(ty, s, want_result);
                want_result = false;
                break;

        case STATEMENT_FOR_LOOP:
                emit_for_loop(ty, s, want_result);
                want_result = false;
                break;

        case STATEMENT_EACH_LOOP:
                if (IsRangeLoop(s)) {
                        emit_range_loop(ty, s, want_result);
                } else {
                        emit_for_each(ty, s, want_result);
                }
                want_result = false;
                break;

        case STATEMENT_WHILE_MATCH:
                emit_while_match(ty, s, want_result);
                want_result = false;
                break;

        case STATEMENT_WHILE:
                emit_while(ty, s, want_result);
                want_result = false;
                break;

        case STATEMENT_IF:
                returns |= (s->iff.neg ? emit_if_not(ty, s, want_result) : emit_if(ty, s, want_result));
                want_result = false;
                break;

        case STATEMENT_EXPRESSION:
                returns |= EE(s->expression);
                if (!want_result && !returns) {
                        INSN(POP);
                } else {
                        want_result = false;
                }
                break;

        case STATEMENT_OPERATOR_DEFINITION:
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
                if (
                        HasBody(s->value)
                     || s->value->type == EXPRESSION_MULTI_FUNCTION
                ) {
        case STATEMENT_DEFINITION:
                        emit_assignment(ty, s->target, s->value, false, true);
                        INSN(POP);
                }
                break;

        case STATEMENT_TAG_DEFINITION:
                for (int i = 0; i < vN(s->tag.s_methods); ++i) {
                        EE(v__(s->tag.s_methods, i));
                }

                for (int i = 0; i < vN(s->tag.methods); ++i) {
                        EE(v__(s->tag.methods, i));
                }

                INSN(DEFINE_TAG);
                Ei32(s->tag.symbol);
                Ei32(-1);
                Ei32(vN(s->tag.methods));
                Ei32(vN(s->tag.s_methods));

                for (int i = vN(s->tag.methods); i > 0; --i) {
                        emit_string(ty, v__(s->tag.methods, i - 1)->name);
                }

                for (int i = vN(s->tag.s_methods); i > 0; --i) {
                        emit_string(ty, v__(s->tag.s_methods, i - 1)->name);
                }
                break;

        case STATEMENT_CLASS_DEFINITION:
                STATE.class = class_get(ty, s->class.symbol);

                for (int i = 0; i < vN(s->class.setters); ++i) {
                        STATE.meth = v__(s->class.setters, i);
                        EE(v__(s->class.setters, i));
                }
                for (int i = 0; i < vN(s->class.getters); ++i) {
                        STATE.meth = v__(s->class.getters, i);
                        EE(v__(s->class.getters, i));
                }
                for (int i = 0; i < vN(s->class.methods); ++i) {
                        STATE.meth = v__(s->class.methods, i);
                        EE(v__(s->class.methods, i));
                }
                for (int i = 0; i < vN(s->class.s_getters); ++i) {
                        STATE.meth = v__(s->class.s_getters, i);
                        EE(v__(s->class.s_getters, i));
                }
                for (int i = 0; i < vN(s->class.s_methods); ++i) {
                        STATE.meth = v__(s->class.s_methods, i);
                        EE(v__(s->class.s_methods, i));
                }

                STATE.meth = NULL;

                INSN(DEFINE_CLASS);
                Ei32(s->class.symbol);
                Ei32(vN(s->class.s_methods));
                Ei32(vN(s->class.s_getters));
                Ei32(vN(s->class.methods));
                Ei32(vN(s->class.getters));
                Ei32(vN(s->class.setters));

                for (int i = vN(s->class.s_methods); i > 0; --i)
                        EM(v__(s->class.s_methods, i - 1)->name);

                for (int i = vN(s->class.s_getters); i > 0; --i)
                        EM(v__(s->class.s_getters, i - 1)->name);

                for (int i = vN(s->class.methods); i > 0; --i)
                        EM(v__(s->class.methods, i - 1)->name);

                for (int i = vN(s->class.getters); i > 0; --i)
                        EM(v__(s->class.getters, i - 1)->name);

                for (int i = vN(s->class.setters); i > 0; --i)
                        EM(v__(s->class.setters, i - 1)->name);

                for (int i = 0; i < vN(s->class.s_fields); ++i) {
                        Expr *f = v__(s->class.s_fields, i);
                        if (f->type == EXPRESSION_EQ) {
                                EE(f->value);
                                INSN(INIT_STATIC_FIELD);
                                Ei32(s->class.symbol);
                                Ei32(f->target->symbol->member);
                        }
                }

                STATE.class = NULL;
                break;

        case STATEMENT_CLEANUP:
                want_result = false;
                INSN(CLEANUP);
                break;

        case STATEMENT_TRY_CLEAN:
        case STATEMENT_TRY:
                returns |= emit_try(ty, s, want_result);
                want_result = false;
                break;

        case STATEMENT_RETURN:
                returns |= emit_return(ty, s);
                break;

        case STATEMENT_GENERATOR_RETURN:
                emit_yield(ty, (Expr const **)vv(s->returns), vN(s->returns), false);
                INSN(JUMP);
                avP(STATE.generator_returns, vN(STATE.code));
                Ei32(0);
                break;

        case STATEMENT_BREAK:
                loop = get_loop(ty, s->depth - 1);

                if (loop == NULL) {
                        fail("invalid break statement (not inside a loop)");
                }

                for (int i = 0; i < s->depth; ++i) {
                        u32 n = get_loop(ty, i)->n;
                        while (n --> 0) {
                                INSN(POP);
                        }
                }

                want_result = false;

                if (s->expression != NULL) {
                        EE(s->expression);
                        if (!loop->wr) {
                                INSN(POP);
                        }
                } else if (loop->wr) {
                        INSN(NIL);
                }

                for (int i = 0; get_try(ty, i) != NULL && get_try(ty, i)->t > loop->t; ++i) {
                        INSN(FINALLY);
                }

                for (int i = loop->resources; i < STATE.resources; ++i) {
                        INSN(DROP);
                }

                INSN(JUMP);
                avP(loop->breaks, vN(STATE.code));
                Ei32(0);
                break;

        case STATEMENT_CONTINUE:
                loop = get_loop(ty, s->depth - 1);

                if (loop == NULL)
                        fail("invalid continue statement (not inside a loop)");

                for (int i = 0; i < s->depth - 1; ++i) {
                        u32 n = get_loop(ty, i)->n;
                        while (n --> 0) {
                                INSN(POP);
                        }
                }

                for (int i = 0; get_try(ty, i) != NULL && get_try(ty, i)->t > loop->t; ++i) {
                        INSN(FINALLY);
                }

                for (int i = loop->resources; i < STATE.resources; ++i) {
                        INSN(DROP);
                }

                INSN(JUMP);
                avP(loop->continues, vN(STATE.code));
                Ei32(0);
                break;

        case STATEMENT_DROP:
                for (int i = 0; i < vN(s->drop); ++i) {
                        emit_load(ty, v__(s->drop, i), STATE.fscope);
                        INSN(TRY_CALL_METHOD);
                        Ei32(0);
                        Ei32(NAMES._drop_);
                        Ei32(0);
                        INSN(POP);
                }
                break;

        case STATEMENT_DEFER:
                EE(s->expression);
                INSN(DEFER);
                break;

        case STATEMENT_NEXT:
                EE(s->expression);
                INSN(NEXT);
                break;
        }

        if (want_result)
                INSN(NIL);

        RestoreContext(ty, ctx);

        add_location(ty, (Expr *)s, start, vN(STATE.code));

#if 0 && defined(TY_PROFILER)
        if (
                (s->type != STATEMENT_BLOCK)
             && (s->type != STATEMENT_MULTI)
             && (s->type != STATEMENT_EXPRESSION || !want_result)
        ) {
                Expr *e = NewExpr(ty, EXPRESSION_STATEMENT);
                e->start = s->start;
                e->end = s->end;
                e->mod = STATE.module;
                e->statement = s;
                add_location(ty, e, start, vN(STATE.code));
        }
#endif

        return returns;
}

static void
emit_new_globals(Ty *ty)
{
        for (usize i = GlobalCount; i < vN(GlobalScope->owned); ++i) {
                Symbol *sym = v__(GlobalScope->owned, i);
                if (sym->i < BuiltinCount) {
                        continue;
                }
                if (sym->tag != -1) {
                        INSN(TAG);
                        Ei32(sym->tag);
                        annotate("%s", sym->identifier);
                        INSN(TARGET_GLOBAL);
                        Ei32(sym->i);
                        INSN(ASSIGN);
                        INSN(POP);
                } else if (sym->class >= 0) {
                        INSN(CLASS);
                        Ei32(sym->class);
                        annotate("%s", sym->identifier);
                        INSN(TARGET_GLOBAL);
                        Ei32(sym->i);
                        INSN(ASSIGN);
                        INSN(POP);
                }
        }

        GlobalCount = vN(GlobalScope->owned);
}

static Scope *
get_module_scope(char const *name)
{
        for (int i = 0; i < vN(modules); ++i) {
                Module *mod = v__(modules, i);
                if (strcmp(name, mod->name) == 0) {
                        return mod->scope;
                }
        }

        return NULL;
}

static void
declare_classes(Ty *ty, Stmt *s, Scope *scope)
{
        Scope *ns = (scope != NULL) ? scope : GetNamespace(ty, s->ns);

        if (s->type == STATEMENT_MULTI) {
                for (int i = 0; i < vN(s->statements); ++i) {
                        declare_classes(ty, v__(s->statements, i), ns);
                }
        } else if (s->type == STATEMENT_CLASS_DEFINITION) {
                if (scope_locally_defined(ty, ns, s->class.name)) {
                        fail(
                                "redeclaration of class %s%s%s%s%s",
                                TERM(1),
                                TERM(34),
                                s->class.name,
                                TERM(22),
                                TERM(39)
                        );
                }
                Symbol *sym = addsymbol(ty, ns, s->class.name);
                sym->class = class_new(ty, s);
                sym->flags |= SYM_CONST;
                s->class.symbol = sym->class;
        }
}

static void
RedpillFun(Ty *ty, Scope *scope, Expr *f, Type *self0)
{
        if (f->scope != NULL) {
                return;
        }

        void *ctx = PushContext(ty, f);

        if (f->type == EXPRESSION_MULTI_FUNCTION) {
                for (int i = 0; i < vN(f->functions); ++i) {
                        Expr *sub = v__(f->functions, i);
                        if (sub->type == EXPRESSION_FUNCTION) {
                                RedpillFun(ty, scope, v__(f->functions, i), self0);
                        } else {
                                InjectRedpill(ty, (Stmt *)sub);
                        }
                }
        }

        Expr *func = STATE.func;

        if (f->name != NULL && !is_method(f)) {
                scope = scope_new(ty, "(function name)", scope, false);
                f->fn_symbol = addsymbol(ty, scope, f->name);
        }

        f->scope = scope_new(ty, f->name == NULL ? "(anon)" : f->name, scope, true);

        STATE.func = f;

        if (vN(f->type_params) > 0) {
                for (usize i = 0; i < vN(f->type_params); ++i) {
                        Expr *param = v__(f->type_params, i);
                        if (param->symbol == NULL) {
                                param->symbol = scope_add_type_var(ty, f->scope, param->identifier);
                                if (param->type == EXPRESSION_MATCH_REST) {
                                        param->symbol->flags |= SYM_VARIADIC;
                                        param->symbol->type->variadic = true;
                                }
                        }
                        symbolize_expression(ty, f->scope, param->constraint);
                }
        }

        if (self0 != NULL) {
                if (
                        !contains(OperatorCharset, *f->name)
                     || (vN(f->params) == 0)
                ) {
                        f->self = scope_add_i(ty, f->scope, "self", vN(f->params));
                        f->self->mod = STATE.module;
                        f->self->loc = STATE.start;
                        if (
                                (TypeType(self0) == TYPE_OBJECT)
                             && (TypeType(self0->class->type) == TYPE_TAG)
                        ) {
                                f->self->type = v__(self0->args, 0);
                        } else {
                                f->self->type = self0;
                        }
                }
        }

        WITH_SELF(f->self) {
                for (usize i = 0; i < vN(f->params); ++i) {
                        symbolize_expression(ty, f->scope, v__(f->dflts, i));
                        avP(f->param_symbols, addsymbol(ty, f->scope, v__(f->params, i)));
                }
                WITH_CTX(TYPE) {
                        for (usize i = 0; i < vN(f->params); ++i) {
                                Expr *constraint = v__(f->constraints, i);
                                symbolize_expression(ty, f->scope, constraint);
                        }
                }
        }

        for (usize i = 0; i < vN(f->params); ++i) {
                Symbol *sym = v__(f->param_symbols, i);
                Expr *constraint = v__(f->constraints, i);
                sym->type = ResolveConstraint(ty, constraint);
                if (constraint != NULL && constraint->type == EXPRESSION_TYPE) {
                        sym->flags |= SYM_FIXED;
                }
        }

        if (f->type == EXPRESSION_MULTI_FUNCTION) {
                f->_type = NULL;
                for (int i = 0; i < vN(f->functions); ++i) {
                        Expr *sub = v__(f->functions, i);
                        if (sub->type == EXPRESSION_FUNCTION) {
                                f->_type = type_both(ty, f->_type, sub->_type);
                        }
                }
                if (f->fn_symbol != NULL) {
                        f->fn_symbol->type = f->_type;
                }
        } else {
                WITH_CTX(TYPE) WITH_SELF(f->self) {
                        symbolize_expression(ty, f->scope, f->return_type);
                        for (int i = 0; i < vN(f->type_bounds); ++i) {
                                TypeBound const *bound = v_(f->type_bounds, i);
                                Expr *var = bound->var;
                                symbolize_expression(ty, f->scope, var);
                                symbolize_expression(ty, f->scope, bound->bound);;
                                switch (var->type) {
                                case EXPRESSION_IDENTIFIER:
                                        if (!SymbolIsTypeVar(var->symbol)) {
                                                fail(
                                                        "type bound applied to non-type parameter %s%s%s",
                                                        TERM(93),
                                                        var->identifier,
                                                        TERM(0)
                                                );
                                        }
                                        break;

                                case EXPRESSION_PLUS:
                                case EXPRESSION_MINUS:
                                case EXPRESSION_STAR:
                                case EXPRESSION_DIV:
                                case EXPRESSION_PERCENT:
                                case EXPRESSION_CMP:
                                case EXPRESSION_XOR:
                                case EXPRESSION_SHL:
                                case EXPRESSION_SHR:
                                case EXPRESSION_USER_OP:
                                        if (
                                                (
                                                        var->left->type != EXPRESSION_IDENTIFIER
                                                     || !SymbolIsTypeVar(var->left->symbol)
                                                )
                                             && (
                                                        var->right->type != EXPRESSION_IDENTIFIER
                                                     || !SymbolIsTypeVar(var->right->symbol)
                                                )
                                        ) {
                                default:
                                                fail("ill-formed type bound: %s", ExpressionTypeName(var));
                                        }
                                        break;
                                }
                        }
                }
                ResolveConstraint(ty, f->return_type);
                f->_type = type_function(ty, f, true);
                if (f->fn_symbol != NULL) {
                        f->fn_symbol->type = f->_type;
                }
        }

        if (f->class < 0) {
                XLOG("REDPILL: === %s() === %s", f->name, type_show(ty, f->_type));
        } else {
                XLOG("REDPILL: === %s.%s() === %s", class_name(ty, f->class), f->name, type_show(ty, f->_type));
        }

        RestoreContext(ty, ctx);

        STATE.func = func;
}

static void
RedpillMethods(Ty *ty, Scope *scope, Type *t0, expression_vector const *ms)
{
        for (int i = 0; i < vN(*ms); ++i) {
                Expr *meth = v__(*ms, i);
                RedpillFun(ty, scope, meth, t0);
        }
}

static void
InjectRedpill(Ty *ty, Stmt *s)
{
        Class *class;
        ClassDefinition *def;
        Scope *scope = GetNamespace(ty, s->ns);

        void *ctx = PushContext(ty, s);
        SCRATCH_SAVE();

        vec(Stmt *) class_defs = {0};

        switch (s->type) {
        case STATEMENT_MULTI:
                for (int i = 0; i < vN(s->statements); ++i) {
                        InjectRedpill(ty, v__(s->statements, i));
                }
                break;

        case STATEMENT_TAG_DEFINITION:
                def = &s->class;
                class = def->var->type->class;
                RedpillMethods(
                        ty,
                        def->scope,
                        class->object_type,
                        &def->methods
                );
                break;

        case STATEMENT_CLASS_DEFINITION:
                def = &s->class;
                XLOG("REDPILL CLASS: ============= %s ============", def->name);
                if (def->redpilled) {
                        break;
                } else {
                        def->redpilled = true;
                }
                class = class_get(ty, s->class.symbol);
                for (int i = 0; i < vN(def->traits); ++i) {
                        Expr *trait = v__(def->traits, i);
                        WITH_CTX(TYPE) {
                                symbolize_expression(ty, def->scope, trait);
                        }
                }
                if (def->super != NULL) {
                        WITH_CTX(TYPE) {
                                symbolize_expression(ty, def->scope, def->super);
                        }

                        int super = ResolveClassSpec(ty, def->super);

                        class_set_super(ty, def->symbol, super);

                        for (int i = 0; i < vN(def->methods); ++i) {
                                Expr *m = v__(def->methods, i);
                                if (m->return_type == NULL && m->type != EXPRESSION_MULTI_FUNCTION) {
                                        Expr const *m0 = FindMethod(class, m->name);
                                        if (m0 != NULL) {
                                                m->return_type = m0->return_type;
                                                dont_printf(
                                                        "%s: inherited return type: %s.%s() -> %s\n",
                                                        class->name,
                                                        class_name(ty, super),
                                                        m->name,
                                                        type_show(ty, type_resolve(ty, m->return_type))
                                                );
                                        }
                                }
                        }
                }
                AddClassTraits(ty, def);
                ResolveFieldTypes(ty, def->scope, &def->fields);
                ResolveFieldTypes(ty, def->scope, &def->s_fields);
                aggregate_overloads(ty, class->i, &def->methods, class_add_method, false);
                aggregate_overloads(ty, class->i, &def->setters, class_add_setter, true);
                aggregate_overloads(ty, class->i, &def->s_methods, class_add_static, false);
                Type *self0 = type_fixed(ty, class->object_type);
                RedpillMethods(ty, def->scope, self0, &def->methods);
                RedpillMethods(ty, def->scope, self0, &def->getters);
                RedpillMethods(ty, def->scope, self0, &def->setters);
                Type *s_self0 = type_fixed(ty, class->type);
                RedpillMethods(ty, def->scope, s_self0, &def->s_methods);
                RedpillMethods(ty, def->scope, s_self0, &def->s_getters);
                RedpillMethods(ty, def->scope, s_self0, &def->s_setters);
                svP(class_defs, s);
                break;

        //case STATEMENT_IF:
        //        for (int i = 0; i < vN(class_defs); ++i) {
        //                Stmt *class_def = v__(class_defs, i);
        //                symbolize_statement(
        //                        ty,
        //                        class_def->class.scope->parent,
        //                        class_def
        //                );
        //        }
        //        v0(class_defs);
        //        if (s->iff.neg) {
        //                symbolize_statement(ty, scope, s->iff.then);
        //                for (int i = 0; i < vN(s->iff.parts); ++i) {
        //                        struct condpart *p = v__(s->iff.parts, i);
        //                        fix_part(ty, p, scope);
        //                        symbolize_pattern(ty, scope, p->target, NULL, p->def);
        //                        if (p->target != NULL) {
        //                                type_assign(ty, p->target, p->e->_type, 0);
        //                        }
        //                }
        //        }
        //        break;

        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_OPERATOR_DEFINITION:
                if (s->target->symbol == NULL) {
                        DeclareSymbols(ty, s);
                }
                DT(s->value->_type, "name=%s\n", s->target->identifier);
                if (s->value->_type == NULL) {
                        RedpillFun(ty, scope, s->value, NULL);
                }
                if (s->value->type != EXPRESSION_MULTI_FUNCTION) {
                        DT(
                                s->target->symbol->type,
                                "PRE  %s::%s  (%p)\n",
                                s->target->symbol->mod->name,
                                s->target->identifier,
                                (void *)s->target->symbol
                        );
                        s->target->symbol->type = type_both(
                                ty,
                                HasBody(s->value) ? NULL : s->target->symbol->type,
                                s->value->_type
                        );
                        DT(
                                s->target->symbol->type,
                                "POST %s::%s  (%p)\n",
                                s->target->symbol->mod->name,
                                s->target->identifier,
                                (void *)s->target->symbol
                        );
                } else {
                        for (int i = 0; i < vN(s->value->functions); ++i) {
                                Stmt *sub = (Stmt *)v__(s->value->functions, i);
                                s->target->symbol->type = type_both(
                                        ty,
                                        s->target->symbol->type,
                                        sub->value->_type
                                );
                                DT(s->target->symbol->type, "sub=%s\n", type_show(ty, sub->value->_type));
                        }
                }
                break;

        default:
                for (int i = 0; i < vN(class_defs); ++i) {
                        Stmt *class_def = v__(class_defs, i);
                        symbolize_statement(
                                ty,
                                class_def->class.scope->parent,
                                class_def
                        );
                }
                v0(class_defs);
                WITH_SCOPE_LIMIT(s->when) {
                        symbolize_statement(ty, scope, s);
                }
                break;

        }

        SCRATCH_RESTORE();
        RestoreContext(ty, ctx);
}

inline static bool
is_proc_def(Stmt const *s)
{
        return (s->type == STATEMENT_FUNCTION_DEFINITION)
            || (s->type == STATEMENT_OPERATOR_DEFINITION);
}

static bool
is_arith(Expr const *e)
{
        switch (e->type) {
        case EXPRESSION_PLUS:
        case EXPRESSION_MINUS:
        case EXPRESSION_STAR:
        case EXPRESSION_DIV:
        case EXPRESSION_PERCENT:
        case EXPRESSION_BIT_OR:
        case EXPRESSION_BIT_AND:
        case EXPRESSION_SHL:
        case EXPRESSION_SHR:
                return true;
        }

        return false;
}

static Expr *
zfold(Expr *e, Scope *scope, void *ctx)
{
        if (
                (e->type == EXPRESSION_PREFIX_MINUS)
             && (e->operand->type == EXPRESSION_INTEGER)
        ) {
                e->type = EXPRESSION_INTEGER;
                e->integer = -e->operand->integer;
                return e;
        }

        if (
                (e->type == EXPRESSION_UNARY_OP)
             && (M_ID(e->uop) == OP_COMPL)
             && (e->operand->type == EXPRESSION_INTEGER)
        ) {
                e->type = EXPRESSION_INTEGER;
                e->integer = ~e->operand->integer;
                return e;
        }

        if (!is_arith(e)) {
                return e;
        }

        if (
                (e->left->type != EXPRESSION_INTEGER)
             || (e->right->type != EXPRESSION_INTEGER)
        ) {
                return e;
        }

        intmax_t a = e->left->integer;
        intmax_t b = e->right->integer;

        switch (e->type) {
        case EXPRESSION_PLUS:     e->integer = a + b;  break;
        case EXPRESSION_MINUS:    e->integer = a - b;  break;
        case EXPRESSION_STAR:     e->integer = a * b;  break;
        case EXPRESSION_DIV:      e->integer = a / b;  break;
        case EXPRESSION_PERCENT:  e->integer = a % b;  break;
        case EXPRESSION_BIT_OR:   e->integer = a | b;  break;
        case EXPRESSION_BIT_AND:  e->integer = a & b;  break;
        case EXPRESSION_SHL:      e->integer = a << b; break;
        case EXPRESSION_SHR:      e->integer = a >> b; break;
        default: UNREACHABLE();
        }

        e->type = EXPRESSION_INTEGER;

        return e;
}

static Stmt *
opt(Ty *ty, Stmt *stmt)
{
        VisitorSet visitor = visit_identitiy(ty);

        visitor.e_post = zfold;
        visitor.t_post = zfold;

        return visit_statement(
                ty,
                stmt,
                scope_new(ty, "(opt)", NULL, false),
                &visitor
        );
}

static Expr *
lowkey(Expr *e, Scope *scope, void *ctx)
{
        if (
                (e->mod == NULL)
             || (e->mod->path == NULL)
             || (strcmp(e->mod->path, QueryFile) != 0)
        ) {
                return e;
        }

        if (
                (e->start.line == QueryLine)
             && (e->start.col <= QueryCol)
             && (
                        (e->end.col >= QueryCol)
                     || (e->end.line > QueryLine)
                )
             && (QueryResult == NULL)
        ) {

                switch (e->type) {
                case EXPRESSION_IDENTIFIER:
                case EXPRESSION_MATCH_REST:
                case EXPRESSION_MATCH_NOT_NIL:
                        QueryResult = e->symbol;
                        break;

                case EXPRESSION_METHOD_CALL:
                        ProposeMemberDefinition(
                                ty,
                                e->method->start,
                                e->method->end,
                                e->object,
                                e->method->identifier
                        );
                        break;

                case EXPRESSION_MEMBER_ACCESS:
                case EXPRESSION_SELF_ACCESS:
                        ProposeMemberDefinition(
                                ty,
                                e->member->start,
                                e->member->end,
                                e->object,
                                e->member->identifier
                        );
                        break;

                case EXPRESSION_FUNCTION:
                        if (e->class >= 0) {
                                Expr o = { ._type = class_get(ty, e->class)->object_type };
                                ProposeMemberDefinition(ty, e->start, e->end, &o, e->name);
                        }
                        break;
                }
        }

        if (
                (e->end.line > QueryLine)
             || (e->end.line == QueryLine && e->end.col > QueryCol)
        ) {
                return e;
        }

        if (QueryExpr == NULL) {
                QueryExpr = e;
        }

        if (e->end.line < QueryExpr->end.line) {
                return e;
        }

        if (
                (e->end.line == QueryExpr->end.line)
             && (e->end.col <= QueryExpr->end.col)
        ) {
                return e;
        }

        QueryExpr = e;

        return e;
}

static Expr *
highkey(Expr *e, bool _, Scope *scope, void *ctx)
{
        return lowkey(e, scope, ctx);
}

static Stmt *
on_god(Ty *ty, Stmt *stmt)
{
        VisitorSet visitor = visit_identitiy(ty);

        visitor.e_post = lowkey;
        visitor.p_post = lowkey;
        visitor.t_post = lowkey;
        visitor.l_post = highkey;

        return visit_statement(
                ty,
                stmt,
                scope_new(ty, "(lsp)", NULL, false),
                &visitor
        );
}


inline static bool
HaveMulti(Stmt **stmts, int i)
{
        for (; stmts[i] != NULL; ++i) {
                if (
                        (stmts[i + 1] != NULL)
                     && (stmts[i    ]->type == STATEMENT_FUNCTION_DEFINITION)
                     && (stmts[i + 1]->type == STATEMENT_FUNCTION_DEFINITION)
                     && strcmp(
                                stmts[i]->target->identifier,
                                stmts[i + 1]->target->identifier
                        ) == 0
                ) {
                        if (HasBody(stmts[i]->value) || HasBody(stmts[i + 1]->value)) {
                                return true;
                        }
                } else {
                        break;
                }
        }

        return false;
}

static Stmt **
compile(Ty *ty, char const *source)
{
        Stmt **p;
        Location parse_error_location;

        PushScope(STATE.global);

        if (!parse_ex(
                ty,
                source,
                CurrentModulePath(ty),
                &p,
                &parse_error_location,
                &STATE.source_tokens
        )) {
                TY_THROW_ERROR();
        }

        DefinePending(ty);

        for (int i = 0; p[i] != NULL; ++i) {
                p[i] = opt(ty, p[i]);
        }

        statement_vector expanded = {0};

        for (usize i = 0; p[i] != NULL; ++i) {
                if (HaveMulti(p, i)) {
                        char buffer[1024];
                        Expr *multi = mkmulti(ty, p[i]->target->identifier, false);
                        bool pub = p[i]->pub;

                        Stmt *def = NewStmt(ty, STATEMENT_FUNCTION_DEFINITION);

                        def->value = multi;
                        def->pub = pub;

                        def->target = NewExpr(ty, EXPRESSION_IDENTIFIER);
                        def->target->start      = p[i]->target->start;
                        def->target->end        = p[i]->target->end;
                        def->target->mod        = STATE.module;
                        def->target->identifier = multi->name;

                        DeclareSymbols(ty, def);

                        int m = 0;
                        do {
                                avP(expanded, p[i + m]);
                                p[i + m]->pub = false;
                                p[i + m]->value->overload = multi;
                                snprintf(buffer, sizeof buffer, "%s#%d", multi->name, m + 1);
                                p[i + m]->target->identifier = p[i + m]->value->name = sclonea(ty, buffer);
                                p[i + m]->target->symbol = NULL;
                                p[i + m]->target->xscope = NULL;
                                avP(multi->functions, (Expr *)p[i + m]);
                                DeclareSymbols(ty, p[i + m]);
                                m += 1;
                        } while (
                                (p[i + m] != NULL)
                            &&  (p[i + m]->type == STATEMENT_FUNCTION_DEFINITION)
                            &&  (strcmp(multi->name, p[i + m]->target->identifier) == 0)
                        );

                        avP(expanded, def);

                } else {
                        avP(expanded, p[i]);
                }
        }

        avP(expanded, NULL);
        p = vv(expanded);

        for (usize i = 0; p[i] != NULL; ++i) {
                InjectRedpill(ty, p[i]);
        }

        for (usize i = 0; p[i] != NULL; ++i) {
                WITH_SCOPE_LIMIT(p[i]->when) {
                        symbolize_statement(ty, STATE.global, p[i]);
                }
                type_iter(ty);
        }

        for (int i = 0; i < vN(STATE.class_ops); ++i) {
                Stmt *def = v__(STATE.class_ops, i);
                WITH_STATE(
                        self, v__(def->value->param_symbols, 0),
                        meth, def->value
                ){
                        symbolize_statement(ty, STATE.global, def);
                }
                type_iter(ty);
        }

        if (SuggestCompletions || FindDefinition) {
                for (usize i = 0; p[i] != NULL; ++i) {
                        on_god(ty, p[i]);
                }
        }

        emit_new_globals(ty);

        /*
         * Move all function definitions to the beginning so that top-level functions have file scope.
         * This allows us to write programs such as
         *
         *      f();
         *
         *      function f() {
         *              g('Hello, world!');
         *      }
         *
         *      function g(s) {
         *              print(s);
         *      }
         *
         * without getting an error due to f and g being referenced before they're defined.
         *
         */
        int end_of_defs = 0;
        for (int i = 0; p[i] != NULL; ++i) {
                if (is_proc_def(p[i])) {
                        int j = i;
                        while (
                                (j --> 0)
                             && !is_proc_def(p[j])
                             && (p[j]->type != STATEMENT_IMPORT)
                        ) {
                                SWAP(Stmt *, p[j], p[j + 1]);
                                end_of_defs = j + 1;
                        }
                }
        }

        for (int i = 0; i < end_of_defs; ++i) {
                emit_statement(ty, p[i], false);
        }

        for (int i = 0; i < vN(STATE.class_ops); ++i) {
                Stmt *def = v__(STATE.class_ops, i);
                WITH_STATE(
                        class, class_get(ty, def->value->class),
                        meth, def->value,
                        self, v__(def->value->param_symbols, 0)
                ) {
                        emit_statement(ty, def, false);
                }
        }

        for (int i = end_of_defs; p[i] != NULL; ++i) {
                emit_statement(ty, p[i], false);
        }

        while (STATE.resources > 0) {
                INSN(DROP);
                STATE.resources -= 1;
        }

        INSN(HALT);

        /*
         * We can re-use this vec(Stmt *) for further compilation but it's important
         * that we empty it here. Because we stripped the constraints out of the
         * functions, passing them to symbolize_op_def() again will provide new
         * implementations of the operators that match /any/ operands.
         */
        vN(STATE.class_ops) = 0;

        /*
         * Add all of the location information from this compliation unit to the GlobalScope list.
         */
        add_location_info(ty);

        vN(STATE.generator_returns) = 0;
        vN(STATE.tries) = 0;
        vN(STATE.loops) = 0;

        add_annotation(ty, "(top)", 0, vN(STATE.code));
        PatchAnnotations(ty);

        PopScope();

        DisableRefinements(ty, STATE.active);

        return p;
}

static Module *
GetModule(Ty *ty, char const *name)
{
        for (int i = 0; i < vN(modules); ++i) {
                Module const *mod = v__(modules, i);
                if (strcmp(mod->name, name) == 0) {
                        return (Module *)mod;
                }
        }

        return NULL;
}

static Module *
GetModuleImport(Ty *ty, Module const *mod, char const *name)
{
        for (int i = 0; i < vN(mod->imports); ++i) {
                struct import const *import = v_(mod->imports, i);
                if (strcmp(import->name, name) == 0) {
                        return import->mod;
                }
        }

        return NULL;
}

inline static Module *
PatchModule(Ty *ty, Module *mod, Stmt **prog)
{
        mod->prog = prog;
        mod->code = vv(STATE.code);
        mod->imports = STATE.imports;
        mod->tokens = STATE.source_tokens;
        return mod;
}

inline static void
AbandonModule(Ty *ty, Module *mod)
{
        u32 n = 0;

        for (u32 i = 0; i < vN(modules); ++i) {
                if (v__(modules, i) != mod) {
                        *v_(modules, n++) = v__(modules, i);
                }
        }

        vN(modules) = n;
}

static Module *
NewModule(
        Ty *ty,
        char const *name,
        char const *path,
        char const *source,
        Scope *scope
)
{
        Module *mod = GetModule(ty, name);

        if (mod == NULL) {
                mod = amA0(sizeof *mod);
                avP(modules, mod);
        }

        if (scope == NULL) {
                scope = scope_new(ty, name, GlobalScope, false);
        }

        mod->source = source;
        mod->name   = name;
        mod->path   = path;
        mod->scope  = scope;

        return mod;
}

static Module *
load_module(Ty *ty, char const *name, Scope *scope)
{
        char const *path;
        char *source = slurp_module(ty, name, &path);

        if (source == NULL) {
                return NULL;
        }

        Module *module = NewModule(ty, name, path, source, scope);

        /*
         * Save the current compiler state so we can restore it after compiling
         * this module.
         */
        CompileState save = STATE;
        STATE = freshstate(ty, module);

        Stmt **prog = compile(ty, source);

        if (scope == NULL) {
                STATE.global->external = true;
        }

        PatchModule(ty, module, prog);

        STATE = save;

        vm_exec(ty, module->code);
        class_finalize_all(ty);

        return module;
}

bool
compiler_import_module(Ty *ty, Stmt const *s)
{
        if (TY_CATCH_ERROR()) {
                return false;
        }

        import_module(ty, s);

        TY_CATCH_END();

        return true;
}

static void
import_module(Ty *ty, Stmt const *s)
{
        char const *name = s->import.module;
        char const *as = s->import.as;
        bool pub = s->import.pub;

        STATE.start = s->start;
        STATE.end = s->end;

        Scope *module_scope = get_module_scope(name);

        /* First make sure we haven't already imported this module, or imported another module
         * with the same local alias. For example,
         *
         *   import foo
         *   import foo
         *
         * and
         *
         *   import foo as bar
         *   import baz as bar
         *
         * are both errors.
         */
        bool forgive = (STATE._eval || STATE._parse);

        for (int i = 0; i < vN(STATE.imports) && !forgive; ++i) {
                bool collision = (strcmp(as, v__(STATE.imports, i).name) == 0);
                bool duplicate = (v__(STATE.imports, i).mod->scope == module_scope);

                if (forgive && (collision || duplicate)) {
                        vvXi(STATE.imports, i);
                        break;
                }

                if (collision) {
                        fail("there is already a module imported under the name '%s'", as);
                }

                if (duplicate) {
                        fail("the module '%s' has already been imported", name);
                }
        }

        if (module_scope == NULL) {
                module_scope = load_module(ty, name, NULL)->scope;
        }

        char const **identifiers = (char const **)vv(s->import.identifiers);
        char const **aliases = (char const **)vv(s->import.aliases);
        int n = vN(s->import.identifiers);

        bool everything = (n == 1)
                       && (strcmp(identifiers[0], "..") == 0);

        if (everything) {
                char const *id = scope_copy_public(ty, STATE.global, module_scope, pub);
                if (id != NULL && !forgive) {
                        fail("module '%s' exports conflcting name '%s'", name, id);
                }
        } else if (s->import.hiding) {
                char const *id = scope_copy_public_except(ty, STATE.global, module_scope, identifiers, n, pub);
                if (id != NULL && !forgive) {
                        fail("module '%s' exports conflcting name '%s'", name, id);
                }
        } else for (int i = 0; i < n; ++i) {
                Symbol *s = scope_lookup(ty, module_scope, identifiers[i]);
                if (s == NULL || !SymbolIsPublic(s)) {
                        if (forgive) {
                                continue;
                        }
                        fail("module '%s' does not export '%s'", name, identifiers[i]);
                }
                scope_insert_as(ty, STATE.global, s, aliases[i])->flags |= SYM_PUBLIC * pub;
        }

        avP(
                STATE.imports,
                ((struct import){
                        .name = as,
                        .mod  = GetScopeModule(ty, module_scope),
                        .pub  = pub
                })
        );
}

void
compiler_init(Ty *ty)
{
        tags_init(ty);

        GlobalScope = scope_new(ty, "GLOBAL", NULL, false);
        GlobalModule = NewModule(ty, "prelude", "(built-in)", NULL, GlobalScope);

        STATE = freshstate(ty, GlobalModule);
        ThreadLocals = scope_new(ty, "(thread)", NULL, false);

        static Type  NIL_TYPE_     = { .type = TYPE_NIL,    .fixed = false };
        static Type  NONE_TYPE_    = { .type = TYPE_NONE,   .fixed = false };
        static Type  BOTTOM_TYPE_  = { .type = TYPE_BOTTOM, .fixed = false };
        static Type  UNKNOWN_TYPE_ = { .type = TYPE_BOTTOM, .fixed = true  };

        NIL_TYPE     = &NIL_TYPE_;
        NONE_TYPE    = &NONE_TYPE_;
        BOTTOM_TYPE  = &BOTTOM_TYPE_;
        UNKNOWN_TYPE = &UNKNOWN_TYPE_;

        for (int i = CLASS_OBJECT; i < CLASS_BUILTIN_END; ++i) {
                Class *c = class_new_empty(ty);
                Symbol *sym = addsymbol(ty, GlobalScope, c->name);
                sym->class = c->i;
                sym->flags |= (SYM_PUBLIC | SYM_CONST | SYM_BUILTIN);
        }

        class_set_super(ty, CLASS_ITER, CLASS_ITERABLE);
        class_set_super(ty, CLASS_TAG, CLASS_FUNCTION);
        class_implement_trait(ty, CLASS_ARRAY,     CLASS_ITERABLE);
        class_implement_trait(ty, CLASS_BLOB,      CLASS_ITERABLE);
        class_implement_trait(ty, CLASS_BLOB,      CLASS_INTO_PTR);
        class_implement_trait(ty, CLASS_DICT,      CLASS_ITERABLE);
        class_implement_trait(ty, CLASS_GENERATOR, CLASS_ITER);
        class_implement_trait(ty, CLASS_PTR,       CLASS_INTO_PTR);
        class_implement_trait(ty, CLASS_STRING,    CLASS_ITERABLE);
        class_implement_trait(ty, CLASS_STRING,    CLASS_INTO_PTR);

        static Class ANY_CLASS = { .i = CLASS_TOP, .name = "Any" };
        static Type  ANY_TYPE  = { .type = TYPE_OBJECT, .class = &ANY_CLASS, .concrete = true };

        TYPE_INT    = class_get(ty, CLASS_INT   )->object_type;
        TYPE_STRING = class_get(ty, CLASS_STRING)->object_type;
        TYPE_REGEX  = class_get(ty, CLASS_REGEX )->object_type;
        TYPE_REGEXV = class_get(ty, CLASS_REGEXV)->object_type;
        TYPE_FLOAT  = class_get(ty, CLASS_FLOAT )->object_type;
        TYPE_BOOL   = class_get(ty, CLASS_BOOL  )->object_type;
        TYPE_BLOB   = class_get(ty, CLASS_BLOB  )->object_type;
        TYPE_ARRAY  = class_get(ty, CLASS_ARRAY )->object_type;
        TYPE_DICT   = class_get(ty, CLASS_DICT  )->object_type;
        TYPE_CLASS_ = class_get(ty, CLASS_CLASS )->object_type;
        TYPE_ANY    = &ANY_TYPE;

        if (CheckTypes) {
                scope_add_type(ty, GlobalScope, "Any")->type = TYPE_ANY;
        } else {
                AnyTypeSymbol = scope_add_type_var(ty, GlobalScope, "Any");
        }
}

void
compiler_load_builtin_modules(Ty *ty)
{
        if (TY_CATCH_ERROR()) {
                fprintf(
                        stderr,
                        "Aborting, failed to load builtin modules: %s\n",
                        TyError(ty)
                );
                exit(1);
        }

        load_module(ty, "ffi",    get_module_scope("ffi"));
        load_module(ty, "os",     get_module_scope("os"));
        load_module(ty, "ty",     get_module_scope("ty"));
        load_module(ty, "pretty", NULL);

        TY_CATCH_END();
}

char *
compiler_load_prelude(Ty *ty)
{
        if (TY_CATCH_ERROR()) {
                fprintf(
                        stderr,
                        "Aborting, failed to load prelude: %s\n",
                        TyError(ty)
                );
                exit(1);
        }

        char const *path;
        char *source = slurp_module(ty, "prelude", &path);

        GlobalModule->path = path;
        GlobalModule->source = source;

        Stmt **prog = compile(ty, source);

        PatchModule(ty, STATE.module, prog);

        STATE.global = scope_new(ty, "(prelude)", STATE.global, false);
        STATE.pscope = scope_new(ty, "(parse)", STATE.global, false);

        v00(STATE.imports);

        avP(STATE.imports, ((struct import) {
                .mod  = GlobalModule,
                .name = "prelude",
                .pub  = false
        }));

        TY_CATCH_END();

        return vv(STATE.code);
}

int
gettag(Ty *ty, char const *module, char const *name)
{
        Symbol *sym = compiler_lookup(ty, module, name);
        if (!(sym != NULL && SymbolIsConst(sym) && sym->tag != -1)) {
                fprintf(
                        stderr,
                        "failed to find tag %s%s%s\n",
                        module ? module : "",
                        module ? "." : "",
                        name
                );
                exit(1);
        }
        return sym->tag;
}

Symbol *
compiler_lookup(Ty *ty, char const *module, char const *name)
{
        Scope *mscope;

        if (module == NULL) {
                return scope_lookup(ty, STATE.global, name);
        } else if (mscope = get_module_scope(module), mscope != NULL) {
                return scope_lookup(ty, mscope, name);
        }

        return NULL;
}

Symbol *
compiler_introduce_symbol(Ty *ty, char const *module, char const *name)
{
        Module *mod;

        if (module == NULL) {
                mod = GlobalModule;
        } else {
                mod = GetModule(ty, module);
                if (mod == NULL) {
                        builtin_modules += 1;
                        mod = NewModule(ty, module, "(built-in)", NULL, NULL);
                        mod->scope->external = true;
                }
        }

        Symbol *sym = addsymbol(ty, mod->scope, name);
        sym->flags |= (SYM_PUBLIC | SYM_BUILTIN);
        sym->type   = BOTTOM_TYPE;
        sym->mod    = mod;

        BuiltinCount += 1;

        return sym;
}

int
compiler_introduce_tag(Ty *ty, char const *module, char const *name, int super)
{
        Scope *s;

        if (module == NULL) {
                s = GlobalScope;
        } else {
                s = get_module_scope(module);
                if (s == NULL) {
                        builtin_modules += 1;
                        s = NewModule(ty, module, "(built-in)", NULL, NULL)->scope;
                        s->external = true;
                }
        }

        Symbol *sym = addsymbol(ty, s, name);
        sym->flags |= (SYM_CONST | SYM_PUBLIC | SYM_BUILTIN);
        sym->tag = tags_new(ty, name);

        Class *class;
        if (super == -1) {
                class = class_new_empty(ty);
                class->name = name;
                class->type = type_tag(ty, class, sym->tag);
        } else {
                class = tags_get_class(ty, super);
        }
        tags_set_class(ty, sym->tag, class);

        sym->type = class->type;

        BuiltinCount += 1;

        return sym->tag;
}

Module *
compiler_compile_source(
        Ty *ty,
        char const *source,
        char const *file
)
{
        v00(STATE.code);
        v00(STATE.expression_locations);

        ContextList = NULL;
        STATE.annotation = (ProgramAnnotation) {0};

        char const *slash = strrchr(file, '/');
#ifdef _WIN32
        slash = (slash == NULL) ? strrchr(file, '\\') : slash;
#endif

        char const *module_name = (slash == NULL) ? file : slash + 1;
        char const *module_path = realpath(file, NULL);

        // (eval) etc.
        if (module_path == NULL) {
                module_path = module_name;
        }

        dont_printf("mod:      %s\n", STATE.module_name);
        dont_printf("mod_path: %s\n", STATE.module_path);

        Module *module = STATE.module = NewModule(
                ty,
                module_name,
                module_path,
                source,
                STATE.global
        );

        if (MainModule == NULL) {
                MainModule = module;
        }

        i64 symbol = scope_get_symbol(ty);
        CompileState save = STATE;

        if (TY_CATCH_ERROR()) {
                scope_set_symbol(ty, symbol);
                AbandonModule(ty, module);
                STATE = save;
                return NULL;
        }

        Stmt **prog = compile(ty, source);
        PatchModule(ty, module, prog);

        class_finalize_all(ty);

        TY_CATCH_END();

        v00(STATE.code);

        return module;
}

#if 0
char *
compiler_compile_source(Ty *ty, char const *source, char const *file)
{
        for (int i = 0; i < 18; ++i) {
                xcompiler_compile_source(ty, source, file);
                STATE = freshstate(ty);
        }
        return xcompiler_compile_source(ty, source, file);
}
#endif

int
compiler_symbol_count(Ty *ty)
{
        return scope_get_symbol(ty);
}

Location
compiler_find_definition(Ty *ty, char const *file, int line, int col)
{
        location_vector *locs = NULL;

        for (int i = 0; i < vN(location_lists); ++i) {
                if (v__(location_lists, i).count == 0) {
                        continue;
                }

                locs = &v__(location_lists, i);

                for (int i = 0; i < locs->count; ++i) {
                        Expr const *e = locs->items[i].e;

                        if (e == NULL || e->mod == NULL) {
                                continue;
                        }

                        if (
                                (
                                        (e->type == EXPRESSION_IDENTIFIER)
                                     || (e->type == EXPRESSION_FUNCTION)
                                     || (e->type == STATEMENT_FUNCTION_DEFINITION)
                                )
                             && (e->start.line == line)
                             && (
                                        col >= e->start.col
                                     && col <= e->end.col
                                )
                             && (e->mod->path != NULL)
                             && (strcmp(e->mod->path, file) == 0)
                        ) {
                                Symbol *sym = (e->type == EXPRESSION_IDENTIFIER)         ? e->symbol
                                            : (e->type == STATEMENT_FUNCTION_DEFINITION) ? ((Stmt *)e)->target->symbol
                                            : e->fn_symbol
                                            ;

                                return (Location) {
                                        .line = sym->loc.line,
                                        .col = sym->loc.col,
                                        .s = (sym->mod != NULL) ? sym->mod->path : NULL
                                };
                        }
                }
        }

        return (Location) {0};
}

ExprLocation *
compiler_find_expr_x(Ty *ty, char const *code, bool func)
{
        location_vector *locs = NULL;

        uptr c = (uptr) code;
        //printf("Looking for %lu\n", c);

        /*
         * First do a linear search for the group of locations which
         * contains this one.
         */
        for (int i = 0; i < vN(location_lists); ++i) {
                if (v__(location_lists, i).count == 0)
                        continue;

                if (c < v__(v__(location_lists, i), 0).p_start)
                        continue;

                uptr end = 0;
                for (int j = 0; j < v__(location_lists, i).count; ++j)
                        if (v__(v__(location_lists, i), j).p_end > end)
                                end = v__(v__(location_lists, i), j).p_end;

                if (c >= end)
                        continue;

                locs = &v__(location_lists, i);

                //printf("Found range (%lu, %lu)\n", locs->items[0].p_start, end);

                break;
        }

        if (locs == NULL) {
                return NULL;
        }

        int match_index = 0;
        ptrdiff_t match_width = PTRDIFF_MAX;

        for (int i = 0; i < locs->count; ++i) {
                if ((c < locs->items[i].p_start) || (c >= locs->items[i].p_end)) {
                        continue;
                }

                if (
                        func != (
                                (locs->items[i].e->type == EXPRESSION_FUNCTION)
                             || (locs->items[i].e->type == EXPRESSION_MULTI_FUNCTION)
                             || (locs->items[i].e->type == EXPRESSION_GENERATOR)
                        )
                ) {
                        continue;
                }

                ptrdiff_t width = (locs->items[i].p_end - locs->items[i].p_start);

                if (width < match_width) {
                        match_index = i;
                        match_width = width;
                }
        }

        if (c < locs->items[match_index].p_start || c >= locs->items[match_index].p_end) {
                return NULL;
        }

        //printf("Found: (%luu, %lu)\n",
        //       (uptr)(locs->items[match_index].p_start),
        //       (uptr)(locs->items[match_index].p_end));

        return &locs->items[match_index];

}

Expr const *
compiler_find_func(Ty *ty, char const *code)
{
        ExprLocation *eloc = compiler_find_expr_x(ty, code, true);
        return (eloc == NULL) ? NULL : eloc->e;
}

Expr const *
compiler_find_expr(Ty *ty, char const *code)
{
        ExprLocation *eloc = compiler_find_expr_x(ty, code, false);
        return (eloc == NULL) ? NULL : eloc->e;
}

char *
compiler_find_next_line(Ty *ty, char const *ip)
{
        // TODO lol

        Expr const *expr = compiler_find_expr(ty, ip);
        if (expr == NULL) {
                return NULL;
        }

        int current = expr->start.line;
        int n = 0;

        for (;;) {
                expr = compiler_find_expr(ty, ++ip);

                if (expr == NULL) {
                        return NULL;
                }

                if (expr->start.line > current) {
                        return (char *)ip;
                }

                if (++n > 4096) {
                        return NULL;
                }
        }
}

static bool
module_match(char const *path, char const *id)
{
        int i = 0;

        while (id[i] != '\0' && (id[i] == path[i] || (id[i] == '.' && path[i] == '/'))) {
                i += 1;
        }

        return id[i] == path[i];
}

/*
 * If we pass 'math.ve', it matches 'math/vector', and we return a pointer into
 * the path here: 'math/vector'
 *                      ^
 */
static char const *
module_prefix(char const *path, char const *id)
{
        char const *last_slash = strrchr(path, '/');
        char const *start = last_slash == NULL ? path : last_slash + 1;

        if (strncmp(path, id, strlen(id)) == 0) {
                return start;
        } else {
                return NULL;
        }
}

int
compiler_get_namespace_completions(
        Ty *ty,
        Expr const *ns,
        char const *prefix,
        char **out,
        int max
)
{
        return scope_get_completions(ty, ns->scope, prefix, out, max, false);
}

int
compiler_get_completions(Ty *ty, char const *mod, char const *prefix, char **out, int max)
{
        if (mod == NULL) {
                return scope_get_completions(ty, STATE.global, prefix, out, max, true);
        }

        for (int i = 0; i < vN(STATE.imports); ++i) {
                if (module_match(v__(STATE.imports, i).name, mod)) {
                        return scope_get_completions(
                                ty,
                                v__(STATE.imports, i).mod->scope,
                                prefix,
                                out,
                                max,
                                false
                        );
                }
        }

        char const *last_dot = strrchr(prefix, '.');

        if (last_dot != NULL) {
        }

        return 0;
}

bool
compiler_has_module(Ty *ty, char const *name)
{
        for (int i = 0; i < vN(STATE.imports); ++i) {
                if (module_match(v__(STATE.imports, i).name, name)) {
                        return true;
                }
        }

        return false;
}

usize
compiler_global_count(Ty *ty)
{
        return vN(GlobalScope->owned);
}

Symbol *
compiler_global_sym(Ty *ty, usize i)
{
        return v__(GlobalScope->owned, i);
}

inline static char *
mkcstr(Ty *ty, Value const *v)
{
        char *s = amA(v->bytes + 1);

        memcpy(s, v->str, v->bytes);
        s[v->bytes] = '\0';

        return s;
}

u32
source_register(Ty *ty, void const *src)
{
#if 0
        char const *s = ((Expr *)src)->start.s;
        if (s == NULL) s = "XXXXX";
        int line = ((Expr *)src)->start.line;
        XLOG("Register: %p -> %p: [%.*s] (%d)", src, *(void **)src, (int)strcspn(s, "\n"), s, line + 1);
#endif

        for (u32 i = 0; i < vN(source_map); ++i) {
                if (v__(source_map, i) == NULL) {
                        v__(source_map, i) = (Expr const *)src;
                        return i + 1;
                }
        }

        xvP(source_map, (Expr const *)src);

        return vN(source_map);
}

void *
source_lookup(Ty *ty, u32 src)
{
        if (src == 0 || src > vN(source_map)) {
                return NULL;
        } else {
                return (void *)v__(source_map, src - 1);
        }
}

void
ForgetSourceNodesFrom(void const *base)
{
        for (u32 i = 0; i < vN(source_map); ++i) {
                Expr const *e = v__(source_map, i);
                if (e != NULL && e->arena == base) {
                        v__(source_map, i) = NULL;
                } else if (e != NULL) {
                        // TODO
                }
        }
}

#define t_(t, i) ((t_)(ty, (t), (uptr)(i)))
inline static Value *
(t_)(Ty *ty, Value const *t, uptr i)
{
        if ((t->type & ~VALUE_TAGGED) != VALUE_TUPLE) {
                if (i == 0) return (Value *)t;
                else goto Missing;
        }

        Value *v = tget_or_null(t, i);
        if (v != NULL) {
                return (Value *)v;
        }

Missing:
        if (i > 16) {
                fail(
                        "missing required entry %s%s%s: %s",
                        TERM(93),
                        (char *)i,
                        TERM(0),
                        VSC(t)
                );
        } else {
                fail(
                        "missing required entry %s%s%s: %s",
                        TERM(95),
                        (int)i,
                        TERM(0),
                        VSC(t)
                );
        }
}

static Value
typarts(Ty *ty, condpart_vector const *parts)
{
        Value v = ARRAY(vA());

        for (int i = 0; i < parts->count; ++i) {
                struct condpart *part = parts->items[i];
                if (part->target != NULL) {
                        vAp(
                                v.array,
                                tagged(
                                        ty,
                                        part->def ? TyLet : TyAssign,
                                        tyexpr(ty, part->target),
                                        tyexpr(ty, part->e),
                                        NONE
                                )
                        );
                } else {
                        vAp(v.array, tyexpr(ty, part->e));
                }
        }

        return v;
}

inline static Value
tyaitem(Ty *ty, Expr const *e, int i)
{
        return tagged(
                ty,
                TyArrayItem,
                vTn(
                        "item", tyexpr(ty, v__(e->elements, i)),
                        "cond", (v__(e->aconds, i) == NULL) ? NIL : tyexpr(ty, v__(e->aconds, i)),
                        "optional", BOOLEAN(v__(e->optional, i))
                ),
                NONE
        );
}

Value
tyexpr(Ty *ty, Expr const *e)
{
        Value v;

        if (e == NULL) {
                return NIL;
        }

        if (e->type > EXPRESSION_MAX_TYPE) {
                return tystmt(ty, (Stmt *)e);
        }

        GC_STOP();

        Scope *scope = STATE.macro_scope == NULL
                     ? STATE.global
                     : STATE.macro_scope;

        fixup_access(ty, scope, (Expr *)e, false);
        expedite_fun(ty, (Expr *)e, scope);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (e->namespace != NULL) {
                        v = vT(2);
                        v__(v, 0) = tyexpr(ty, e->namespace);
                        v__(v, 1) = vSsz(e->identifier);
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TyMemberAccess);
                        break;
                }
                v = vTn(
                        "name", vSsz(e->identifier),
                        "module", (e->module == NULL) ? NIL : vSsz(e->module),
                        "constraint", (e->constraint == NULL) ? NIL : tyexpr(ty, e->constraint)
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyId);

                break;
        case EXPRESSION_MODULE:
        case EXPRESSION_NAMESPACE:
                if (e->parent != NULL) {
                        v = vT(2);
                        v__(v, 0) = tyexpr(ty, e->parent);
                        v__(v, 1) = vSsz(e->name);
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TyMemberAccess);
                        break;
                } else {
                        v = vTn(
                                "name", vSsz(e->name),
                                "module", NIL,
                                "constraint", NIL
                        );

                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TyId);
                }
                break;
        case EXPRESSION_MATCH_ANY:
                if (e->constraint != NULL) {
                        v = tagged(ty, TyAny, tyexpr(ty, e->constraint), NONE);
                } else {
                        v = TAG(TyAny);
                }
                break;
        case EXPRESSION_ALIAS_PATTERN:
                v = vTn(
                        "name",       vSsz(e->identifier),
                        "pattern",    tyexpr(ty, e->aliased),
                        "module",     (e->module == NULL) ? NIL : vSsz(e->module),
                        "constraint", (e->constraint == NULL) ? NIL : tyexpr(ty, e->constraint)
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyPatternAlias);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                v = vTn(
                        "name", vSsz(e->identifier),
                        "module", (e->module == NULL) ? NIL : vSsz(e->module)
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyNotNil);
                break;
        case EXPRESSION_RESOURCE_BINDING:
                v = tagged(
                        ty,
                        TyResource,
                        vTn(
                                "name", vSsz(e->identifier),
                                "module", (e->module == NULL) ? NIL : vSsz(e->module)
                        ),
                        NONE
                );
                break;
        case EXPRESSION_TYPE_UNION:
                v = ARRAY(vA());
                NOGC(v.array);
                for (int i = 0; i < vN(e->es); ++i) {
                        vAp(v.array, tyexpr(ty, v__(e->es, i)));
                }
                OKGC(v.array);
                v = tagged(ty, TyUnion, v, NONE);
                break;
        case EXPRESSION_ARRAY:
                v = ARRAY(vA());
                NOGC(v.array);
                for (int i = 0; i < vN(e->elements); ++i) {
                        vAp(v.array, tyaitem(ty, e, i));
                }
                OKGC(v.array);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyArray);
                break;
        case EXPRESSION_SPREAD:
                v = tyexpr(ty, e->value);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, v.tags, TySpread);
                break;
        case EXPRESSION_SPLAT:
                v = tyexpr(ty, e->value);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, v.tags, TySplat);
                break;
        case EXPRESSION_ARRAY_COMPR:
        {
                Array *avElems = vA();

                for (int i = 0; i < vN(e->elements); ++i) {
                        vAp(avElems, tyaitem(ty, e, i));
                }

                v = vTn(
                        "items", ARRAY(avElems),
                        "pattern", tyexpr(ty, e->compr.pattern),
                        "iter", tyexpr(ty, e->compr.iter),
                        "cond", tyexpr(ty, e->compr.cond),
                        "where", tystmt(ty, e->compr.where)
                );

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, v.tags, TyArrayCompr);

                break;
        }
        case EXPRESSION_DICT_COMPR:
        {
                Array *avElems = vA();

                for (int i = 0; i < vN(e->keys); ++i) {
                        vAp(
                                avElems,
                                tagged(
                                        ty,
                                        TyDictItem,
                                        tyexpr(ty, v__(e->keys, i)),
                                        tyexpr(ty, v__(e->values, i)),
                                        NONE
                                )
                        );
                }

                v = vTn(
                        "items", ARRAY(avElems),
                        "default", tyexpr(ty, e->dflt),
                        "pattern", tyexpr(ty, e->dcompr.pattern),
                        "iter", tyexpr(ty, e->dcompr.iter),
                        "cond", tyexpr(ty, e->dcompr.cond),
                        "where", tystmt(ty, e->dcompr.where)
                );

                v = tagged(ty, TyDictCompr, v, NONE);

                break;
        }
        case EXPRESSION_TAG_APPLICATION:
        {
                if (e->tagged->type == EXPRESSION_TUPLE) {
                        v = vT(vN(e->tagged->es) +  1);
                        for (int i = 0; i < vN(e->tagged->es); ++i) {
                                v__(v, i + 1) = tyexpr(ty, v__(e->tagged->es, i));
                        }
                } else {
                        v = vT(2);
                        v__(v, 1) = tyexpr(ty, e->tagged);
                }

                if (e->identifier != EmptyString) {
                        Expr *id = amA(sizeof *id);
                        *id = *e;
                        id->type = EXPRESSION_IDENTIFIER;
                        v__(v, 0) = tyexpr(ty, id);
                } else {
                        v__(v, 0) = tagged(ty, TyValue, *e->constraint->v, NONE);
                }

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, v.tags, TyTagged);

                break;
        }
        case EXPRESSION_EVAL:
                v = tagged(
                        ty,
                        TyEval,
                        tyexpr(ty, e->operand),
                        NONE
                );
                break;
        case EXPRESSION_GENERATOR:
                v = tystmt(ty, e->body);
                v.tags = tags_push(ty, v.tags, TyGenerator);
                break;
        case EXPRESSION_FUNCTION:
        case EXPRESSION_IMPLICIT_FUNCTION:
        {
                Array *decorators = vA();
                Array *params = vA();

                int tag = (e->type == EXPRESSION_IMPLICIT_FUNCTION) ? TyImplicitFunc : TyFunc;

                v = tagged(
                        ty,
                        tag,
                        vTn(
                                "name", e->name != NULL ? vSsz(e->name) : NIL,
                                "params", ARRAY(params),
                                "rt", e->return_type != NULL ? tyexpr(ty, e->return_type) : NIL,
                                "body", tystmt(ty, e->body),
                                "decorators", ARRAY(decorators)
                        ),
                        NONE
                );

                for (int i = 0; i < vN(e->decorators); ++i) {
                        vAp(decorators, tyexpr(ty, v__(e->decorators, i)));
                }

                for (int i = 0; i < vN(e->params); ++i) {
                        Value name = vSsz(v__(e->params, i));
                        if (i == e->rest) {
                                vAp(
                                        params,
                                        tagged(ty, TyGather, name, NONE)
                                );
                        } else if (i == e->ikwargs) {
                                vAp(
                                        params,
                                        tagged(ty, TyKwargs, name, NONE)
                                );
                        } else {
                                Value p = vTn(
                                        "name", name,
                                        "constraint", v__(e->constraints, i) != NULL ? tyexpr(ty, v__(e->constraints, i)) : NIL,
                                        "default", v__(e->dflts, i) != NULL ? tyexpr(ty, v__(e->dflts, i)) : NIL
                                );
                                vAp(params, tagged(ty, TyParam, p, NONE));
                        }
                }

                break;
        }
        case EXPRESSION_TAG_PATTERN_CALL:
                try_symbolize_application(ty, NULL, (Expr *)e);
        case EXPRESSION_TAG_PATTERN:
                v = vT(2);
                v__(v, 0) = vSsz(e->identifier);
                v__(v, 1) = tyexpr(ty, e->tagged);
                v = tagged(
                        ty,
                        TyTagPattern,
                        v,
                        NONE
                );
                break;
        case EXPRESSION_TUPLE:
                v = ARRAY(vA());
                NOGC(v.array);
                for (int i = 0; i < vN(e->es); ++i) {
                        Value name = (v__(e->names, i) == NULL)
                                   ? NIL
                                   : vSsz(v__(e->names, i));
                        vAp(
                                v.array,
                                tagged(
                                        ty,
                                        TyRecordEntry,
                                        vTn(
                                                "item", tyexpr(ty, v__(e->es, i)),
                                                "name", name,
                                                "cond", (v__(e->tconds, i) == NULL) ? NIL : tyexpr(ty, v__(e->tconds, i)),
                                                "optional", BOOLEAN(!v__(e->required, i))
                                        ),
                                        NONE
                                )
                        );
                }
                OKGC(v.array);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyRecord);
                break;
        case EXPRESSION_LIST:
                v = ARRAY(vA());
                NOGC(v.array);
                for (int i = 0; i < vN(e->es); ++i) {
                        vAp(v.array, tyexpr(ty, v__(e->es, i)));
/*
                        vAp(
                                v.array,
                                tagged(
                                        ty,
                                        TyRecordEntry,
                                        vTn(
                                                "item", tyexpr(ty, v__(e->es, i)),
                                                "name", NIL,
                                                "cond", NIL,
                                                "optional", NIL,
                                                NULL
                                        ),
                                        NONE
                                )
                        );
*/
                }
                OKGC(v.array);
/*
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyRecord);
*/
                break;
        case EXPRESSION_CHOICE_PATTERN:
                v = ARRAY(vA());
                NOGC(v.array);
                for (int i = 0; i < vN(e->es); ++i) {
                        vAp(v.array, tyexpr(ty, v__(e->es, i)));
                }
                OKGC(v.array);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyChoicePattern);
                break;
        case EXPRESSION_YIELD:
                v = ARRAY(vA());
                for (int i = 0; i < vN(e->es); ++i) {
                        vAp(v.array, tyexpr(ty, v__(e->es, i)));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyYield);
                break;
        case EXPRESSION_THROW:
                v = tagged(ty, TyThrow, tyexpr(ty, e->throw), NONE);
                break;
        case EXPRESSION_MATCH:
                v = vT(2);
                v__(v, 0) = tyexpr(ty, e->subject);
                v__(v, 1) = ARRAY(vA());
                for (int i = 0; i < vN(e->patterns); ++i) {
                        Value case_ = vT(2);
                        v__(case_, 0) = tyexpr(ty, v__(e->patterns, i));
                        v__(case_, 1) = tyexpr(ty, v__(e->thens, i));
                        vAp(
                                v__(v, 1).array,
                                case_
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyMatch);
                break;
        case EXPRESSION_DICT:
                v = tagged(
                        ty,
                        TyDict,
                        vTn(
                                "items", ARRAY(vA()),
                                "default", e->dflt != NULL ? tyexpr(ty, e->dflt) : NIL
                        ),
                        NONE
                );
                NOGC(v__(v, 0).array);
                for (int i = 0; i < vN(e->keys); ++i) {
                        vAp(
                                v__(v, 0).array,
                                tagged(
                                        ty,
                                        TyDictItem,
                                        tyexpr(ty, v__(e->keys, i)),
                                        tyexpr(ty, v__(e->values, i)),
                                        NONE
                                )
                        );
                }
                OKGC(v__(v, 0).array);
                break;
        case EXPRESSION_FUNCTION_CALL:
                v = vTn(
                        "func", tyexpr(ty, e->function),
                        "args", ARRAY(vA())
                );
                for (int i = 0; i < vN(e->args); ++i) {
                        vAp(
                                v__(v, 1).array,
                                tagged(
                                        ty,
                                        TyArg,
                                        vTn(
                                                "arg", tyexpr(ty, v__(e->args, i)),
                                                "cond", v__(e->fconds, i) != NULL ? tyexpr(ty, v__(e->fconds, i)) : NIL,
                                                "name", NIL
                                        ),
                                        NONE
                                )
                        );
                }
                for (int i = 0; i < vN(e->kws); ++i) {
                        vAp(
                                v__(v, 1).array,
                                tagged(
                                        ty,
                                        TyArg,
                                        vTn(
                                                "arg", tyexpr(ty, v__(e->kwargs, i)),
                                                "cond", v__(e->fkwconds, i) != NULL ? tyexpr(ty, v__(e->fkwconds, i)) : NIL,
                                                "name", vSsz(v__(e->kws, i))
                                        ),
                                        NONE
                                )
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyCall);
                break;
        case EXPRESSION_METHOD_CALL:
        case EXPRESSION_DYN_METHOD_CALL:
                v = vTn(
                        "object", tyexpr(ty, e->function),
                        "method", (e->type == EXPRESSION_METHOD_CALL) ? vSsz(e->method->identifier)
                                                                      : tyexpr(ty, e->method),
                        "args", ARRAY(vA())
                );
                for (int i = 0; i < vN(e->method_args); ++i) {
                        vAp(
                                v__(v, 2).array,
                                tagged(
                                        ty,
                                        TyArg,
                                        vTn(
                                                "arg", tyexpr(ty, v__(e->method_args, i)),
                                                "cond", v__(e->mconds, i) != NULL ? tyexpr(ty, v__(e->mconds, i)) : NIL,
                                                "name", NIL
                                        ),
                                        NONE
                                )
                        );
                }
                for (int i = 0; i < vN(e->method_kws); ++i) {
                        vAp(
                                v__(v, 2).array,
                                tagged(
                                        ty,
                                        TyArg,
                                        vTn(
                                                "arg", tyexpr(ty, v__(e->method_kwargs, i)),
                                                // TODO conditional method kwargs
                                                "cond", NIL,
                                                "name", vSsz(v__(e->method_kws, i))
                                        ),
                                        NONE
                                )
                        );
                }

                v.type |= VALUE_TAGGED;

                v.tags = tags_push(
                        ty,
                        0,
                        (e->type == EXPRESSION_METHOD_CALL)
                                ? (e->maybe ? TyTryMethodCall : TyMethodCall)
                                : (e->maybe ? TyTryDynMethodCall : TyDynMethodCall)
                );

                break;
        case EXPRESSION_DYN_MEMBER_ACCESS:
                v = vT(2);
                v__(v, 0) = tyexpr(ty, e->object);
                v__(v, 1) = tyexpr(ty, e->member);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, e->maybe ? TyTryDynMemberAccess : TyDynMemberAccess);
                break;
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                v = vT(2);
                v__(v, 0) = tyexpr(ty, e->object);
                v__(v, 1) = vSsz(e->member->identifier);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, e->maybe ? TyTryMemberAccess : TyMemberAccess);
                break;
        case EXPRESSION_SUBSCRIPT:
                v = vT(2);
                v__(v, 0) = tyexpr(ty, e->container);
                v__(v, 1) = tyexpr(ty, e->subscript);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TySubscript);
                break;
        case EXPRESSION_SLICE:
                v = vT(4);
                v__(v, 0) = tyexpr(ty, e->slice.e);
                v__(v, 1) = tyexpr(ty, e->slice.i);
                v__(v, 2) = tyexpr(ty, e->slice.j);
                v__(v, 3) = tyexpr(ty, e->slice.k);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TySlice);
                break;
        case EXPRESSION_WITH:
                v = ARRAY(vA());
                for (int i = 0; i < vN(e->with.defs); ++i) {
                        vAp(v.array, tystmt(ty, v__(e->with.defs, i)));
                }
                v = tagged(
                        ty,
                        TyWith,
                        v,
                        tystmt(ty, v__(e->with.block->statements, 1)->try.s),
                        NONE
                );
                break;
        case EXPRESSION_NIL:
                v = TAG(TyNil);
                break;
        case EXPRESSION_CONDITIONAL:
                v = tagged(
                        ty,
                        TyCond,
                        tyexpr(ty, e->cond),
                        tyexpr(ty, e->then),
                        tyexpr(ty, e->otherwise),
                        NONE
                );
                break;
        case EXPRESSION_OPERATOR:
                v = tagged(ty, TyOperator, vSsz(e->op.id), NONE);
                break;
        case EXPRESSION_REGEX:
                v = tagged(ty, TyRegex, REGEX(e->regex), NONE);
                break;
        case EXPRESSION_INTEGER:
                v = INTEGER(e->integer);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyInt);
                break;
        case EXPRESSION_REAL:
                v = REAL(e->real);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyFloat);
                break;
        case EXPRESSION_BOOLEAN:
                v = BOOLEAN(e->boolean);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyBool);
                break;
        case EXPRESSION_STRING:
                v = vSsz(e->string);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyString);
                break;
        case EXPRESSION_SPECIAL_STRING:
                v = ARRAY(vA());
                gP(&v);

                vAp(v.array, vSsz(v__(e->strings, 0)));

                for (int i = 0; i < vN(e->expressions); ++i) {
                        Value expr = tyexpr(ty, v__(e->expressions, i));
                        Value arg = tyexpr(ty, *v_(e->fmtfs, i));
                        Value fmt;
                        Value width;
                        if (v__(e->fmts, i) == NULL) {
                                fmt = NIL;
                                width = NIL;
                        } else {
                                fmt = tyexpr(ty, v__(e->fmts, i));
                                width = INTEGER(v__(e->widths, i));
                        }
                        vAp(v.array, QUADRUPLE(expr, fmt, width, arg));
                        vAp(v.array, vSsz(v__(e->strings, i + 1)));
                }

                gX();

                if (e->lang == NULL) {
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TySpecialString);
                } else {
                        v = tagged(
                                ty,
                                TyLangString,
                                tyexpr(ty, e->lang),
                                v,
                                NONE
                        );
                }

                break;
        case EXPRESSION_USER_OP:
                v = tagged(
                        ty,
                        TyUserOp,
                        vSsz(e->op_name),
                        tyexpr(ty, e->left),
                        tyexpr(ty, e->right),
                        NONE
                );
                break;
        case EXPRESSION_DOT_DOT:
                v = tagged(ty, TyRange, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_DOT_DOT_DOT:
                v = tagged(ty, TyIncRange, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_EQ:
                v = tagged(ty, TyAssign, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_PLUS_EQ:
                v = tagged(ty, TyMutAdd, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_MINUS_EQ:
                v = tagged(ty, TyMutSub, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_STAR_EQ:
                v = tagged(ty, TyMutMul, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_DIV_EQ:
                v = tagged(ty, TyMutDiv, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_MOD_EQ:
                v = tagged(ty, TyMutMod, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_AND_EQ:
                v = tagged(ty, TyMutAnd, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_OR_EQ:
                v = tagged(ty, TyMutOr, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_XOR_EQ:
                v = tagged(ty, TyMutXor, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_SHL_EQ:
                v = tagged(ty, TyMutShl, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_SHR_EQ:
                v = tagged(ty, TyMutShr, tyexpr(ty, e->target), tyexpr(ty, e->value), NONE);
                break;
        case EXPRESSION_GT:
                v = tagged(ty, TyGT, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_GEQ:
                v = tagged(ty, TyGEQ, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_LT:
                v = tagged(ty, TyLT, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_LEQ:
                v = tagged(ty, TyLEQ, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_CMP:
                v = tagged(ty, TyCmp, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_WTF:
                v = tagged(ty, TyWtf, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_PLUS:
                v = tagged(ty, TyAdd, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_STAR:
                v = tagged(ty, TyMul, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_MINUS:
                v = tagged(ty, TySub, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_DIV:
                v = tagged(ty, TyDiv, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_PERCENT:
                v = tagged(ty, TyMod, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_XOR:
                v = tagged(ty, TyXor, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_SHL:
                v = tagged(ty, TyShl, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_SHR:
                v = tagged(ty, TyShr, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_DBL_EQ:
                v = tagged(ty, TyEq, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_NOT_EQ:
                v = tagged(ty, TyNotEq, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_CHECK_MATCH:
                v = tagged(ty, TyMatches, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_IN:
                v = tagged(ty, TyIn, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_NOT_IN:
                v = tagged(ty, TyNotIn, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_OR:
                v = tagged(ty, TyOr, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_AND:
                v = tagged(ty, TyAnd, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_KW_AND:
                v = tagged(ty, TyKwAnd, tyexpr(ty, e->left), typarts(ty, &e->p_cond), NONE);
                break;
        case EXPRESSION_BIT_AND:
                v = tagged(ty, TyBitAnd, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_BIT_OR:
                v = tagged(ty, TyBitOr, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_VIEW_PATTERN:
                v = tagged(ty, TyView, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                v = tagged(ty, TyNotNilView, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_CAST:
                v = tagged(ty, TyCast, tyexpr(ty, e->left), tyexpr(ty, e->right), NONE);
                break;
        case EXPRESSION_TYPE_OF:
                v = tagged(ty, TyTypeOf, tyexpr(ty, e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_HASH:
                v = tyexpr(ty, e->operand);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, v.tags, TyCount);
                break;
        case EXPRESSION_PREFIX_BANG:
                v = tagged(ty, TyNot, tyexpr(ty, e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_MINUS:
                v = tagged(ty, TyNeg, tyexpr(ty, e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_QUESTION:
                v = tagged(ty, TyQuestion, tyexpr(ty, e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_INC:
                v = tagged(ty, TyPreInc, tyexpr(ty, e->operand), NONE);
                break;
        case EXPRESSION_POSTFIX_INC:
                v = tagged(ty, TyPostInc, tyexpr(ty, e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_DEC:
                v = tagged(ty, TyPreDec, tyexpr(ty, e->operand), NONE);
                break;
        case EXPRESSION_POSTFIX_DEC:
                v = tagged(ty, TyPostDec, tyexpr(ty, e->operand), NONE);
                break;
        case EXPRESSION_DEFINED:
                v = tagged(
                        ty,
                        TyDefined,
                        vTn(
                                "name", vSsz(e->identifier),
                                "module", (e->module == NULL) ? NIL : vSsz(e->module)
                        ),
                        NONE
                );
                break;
        case EXPRESSION_IFDEF:
                v = tagged(
                        ty,
                        TyIfDef,
                        vTn(
                                "name", vSsz(e->identifier),
                                "module", (e->module == NULL) ? NIL : vSsz(e->module)
                        ),
                        NONE
                );
                break;
        case EXPRESSION_TEMPLATE_HOLE:
                if (vN(ty->stack) > e->hole.i) {
                        v = *vm_get(ty, e->hole.i);
                } else {
                        v = TAG(TyNil);
                }
                break;
        case EXPRESSION_TEMPLATE_XHOLE:
                v = tagged(ty, TyExpr, PTR(e->hole.expr), NONE);
                break;
        case EXPRESSION_TEMPLATE_VHOLE:
                if (vN(ty->stack) > e->hole.i) {
                        v = tagged(ty, TyValue, *vm_get(ty, e->hole.i), NONE);
                } else {
                        v = TAG(TyNil);
                }
                break;
        case EXPRESSION_TEMPLATE_THOLE:
                if (vN(ty->stack) > e->hole.i) {
                        v = tagged(ty, TyType, *vm_get(ty, e->hole.i), NONE);
                } else {
                        v = TAG(TyUnknownT);
                }
                break;
        case EXPRESSION_STATEMENT:
                v = tystmt(ty, e->statement);
                break;
        case EXPRESSION_VALUE:
                v = tagged(ty, TyValue, *e->v, NONE);
                break;
        default:
                v = tagged(ty, TyExpr, PTR((void *)e), NONE);
        }

        GC_RESUME();

        v.src = source_register(ty, e);

        return v;
}

Value
tystmt(Ty *ty, Stmt *s)
{
        Value v;

        if (s == NULL) {
                return NIL;
        }

        GC_STOP();

        switch (s->type) {
        case STATEMENT_DEFINITION:
                v = vT(2);
                v__(v, 0) = tyexpr(ty, s->target);
                v__(v, 1) = tyexpr(ty, s->value);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyLet);
                break;
        case STATEMENT_CLASS_DEFINITION:
                v = vTn(
                        "name", vSsz(s->class.name),
                        "super", s->class.super != NULL ? tyexpr(ty, s->class.super) : NIL,
                        "methods", ARRAY(vA()),
                        "getters", ARRAY(vA()),
                        "setters", ARRAY(vA()),
                        "fields",  ARRAY(vA()),
                        "staticMethods", ARRAY(vA()),
                        "staticGetters", ARRAY(vA()),
                        "staticSetters", ARRAY(vA()),
                        "staticFields",  ARRAY(vA())
                );
                for (int i = 0; i < vN(s->class.methods); ++i) {
                        vAp(v__(v, 2).array, tyexpr(ty, v__(s->class.methods, i)));
                }
                for (int i = 0; i < vN(s->class.getters); ++i) {
                        vAp(v__(v, 3).array, tyexpr(ty, v__(s->class.getters, i)));
                }
                for (int i = 0; i < vN(s->class.setters); ++i) {
                        vAp(v__(v, 4).array, tyexpr(ty, v__(s->class.setters, i)));
                }
                for (int i = 0; i < vN(s->class.fields); ++i) {
                        vAp(v__(v, 5).array, tyexpr(ty, v__(s->class.fields, i)));
                }
                for (int i = 0; i < vN(s->class.s_methods); ++i) {
                        vAp(v__(v, 6).array, tyexpr(ty, v__(s->class.s_methods, i)));
                }
                for (int i = 0; i < vN(s->class.s_getters); ++i) {
                        vAp(v__(v, 7).array, tyexpr(ty, v__(s->class.s_getters, i)));
                }
                for (int i = 0; i < vN(s->class.s_setters); ++i) {
                        vAp(v__(v, 8).array, tyexpr(ty, v__(s->class.s_setters, i)));
                }
                for (int i = 0; i < vN(s->class.s_fields); ++i) {
                        vAp(v__(v, 9).array, tyexpr(ty, v__(s->class.s_fields, i)));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyClass);
                break;
        case STATEMENT_DEFER:
                v = tyexpr(ty, s->expression);
                v.tags = tags_push(ty, v.tags, TyDefer);
                break;
        case STATEMENT_RETURN:
                v = vT(vN(s->returns));
                for (int i = 0; i < vN(s->returns); ++i) {
                        v__(v, i) = tyexpr(ty, v__(s->returns, i));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyReturn);
                break;
        case STATEMENT_BREAK:
                v = tagged(
                        ty,
                        TyBreak,
                        vTn(
                                "value", (s->expression == NULL) ? NIL : tyexpr(ty, s->expression),
                                "depth", INTEGER(s->depth)
                        ),
                        NONE
                );
                break;
        case STATEMENT_CONTINUE:
                v = tagged(
                        ty,
                        TyContinue,
                        INTEGER(s->depth),
                        NONE
                );
                break;
        case STATEMENT_MATCH:
                v = vT(2);
                v__(v, 0) = tyexpr(ty, s->match.e);
                v__(v, 1) = ARRAY(vA());
                for (int i = 0; i < vN(s->match.patterns); ++i) {
                        Value case_ = vT(2);
                        v__(case_, 0) = tyexpr(ty, v__(s->match.patterns, i));
                        v__(case_, 1) = tystmt(ty, v__(s->match.statements, i));
                        vAp(v__(v, 1).array, case_);
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyMatch);
                break;
        case STATEMENT_WHILE_MATCH:
                v = vT(2);
                v__(v, 0) = tyexpr(ty, s->match.e);
                v__(v, 1) = ARRAY(vA());
                for (int i = 0; i < vN(s->match.patterns); ++i) {
                        Value case_ = vT(2);
                        v__(case_, 0) = tyexpr(ty, v__(s->match.patterns, i));
                        v__(case_, 1) = tystmt(ty, v__(s->match.statements, i));
                        vAp(v__(v, 1).array, case_);
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyWhileMatch);
                break;
        case STATEMENT_EACH_LOOP:
        {
                Array *ps = vA();

                v = vTn(
                        "pattern", ARRAY(ps),
                        "iter", tyexpr(ty, s->each.array),
                        "expr", tystmt(ty, s->each.body),
                        "cond", s->each.cond != NULL ? tyexpr(ty, s->each.cond) : NIL,
                        "stop", s->each.stop != NULL ? tyexpr(ty, s->each.stop) : NIL
                );

                for (int i = 0; i < vN(s->each.target->es); ++i) {
                        vAp(ps, tyexpr(ty, v__(s->each.target->es, i)));
                }

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyEach);

                break;
        }
        case STATEMENT_FOR_LOOP:
                v = tagged(ty, TyFor, vT(4), NONE);
                v__(v, 0) = tystmt(ty, s->for_loop.init);
                v__(v, 1) = tyexpr(ty, s->for_loop.cond);
                v__(v, 2) = tyexpr(ty, s->for_loop.next);
                v__(v, 3) = tystmt(ty, s->for_loop.body);
                break;
        case STATEMENT_BLOCK:
                v = ARRAY(vA());
                for (int i = 0; i < vN(s->statements); ++i) {
                        vAp(v.array, tystmt(ty, v__(s->statements, i)));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyBlock);
                break;
        case STATEMENT_MULTI:
                v = ARRAY(vA());
                for (int i = 0; i < vN(s->statements); ++i) {
                        vAp(v.array, tystmt(ty, v__(s->statements, i)));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyMulti);
                break;
        case STATEMENT_WHILE:
                v = vT(2);
                v__(v, 0) = typarts(ty, &s->While.parts);
                v__(v, 1) = tystmt(ty, s->While.block);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyWhile);
                break;
        case STATEMENT_IF:
                v = vT(3);
                v__(v, 0) = typarts(ty, &s->iff.parts);
                v__(v, 1) = tystmt(ty, s->iff.then);
                v__(v, 2) = s->iff.otherwise != NULL ? tystmt(ty, s->iff.otherwise) : NIL;
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, s->iff.neg ? TyIfNot : TyIf);
                break;
        case STATEMENT_TRY:
        {
                Array *avCatches = vA();

                for (int i = 0; i < vN(s->try.handlers); ++i) {
                        Value catch = vT(2);
                        v__(catch, 0) = tyexpr(ty, v__(s->try.patterns, i));
                        v__(catch, 1) = tystmt(ty, v__(s->try.handlers, i));
                        vAp(avCatches, catch);
                }

                v = tagged(
                        ty,
                        TyTry,
                        vTn(
                                "body", tystmt(ty, s->try.s),
                                "catches", ARRAY(avCatches),
                                "always", (s->try.finally == NULL) ? NIL : tystmt(ty, s->try.finally)
                        ),
                        NONE
                );

                break;
        }
        case STATEMENT_FUNCTION_DEFINITION:
                v = tyexpr(ty, s->value);
                v.tags = tags_push(ty, 0, TyFuncDef);
                break;
        case STATEMENT_NULL:
                v = TAG(TyNull);
                break;
        case STATEMENT_EXPRESSION:
                v = tyexpr(ty, s->expression);
                break;
        default:
                v = tagged(ty, TyStmt, PTR((void *)s), NONE);
        }

        GC_RESUME();

        v.src = source_register(ty, s);

        return v;
}

condpart_vector
cparts(Ty *ty, Value *v)
{
        condpart_vector parts = {0};

        for (int i = 0; i < v->array->count; ++i) {
                Value *part = &v->array->items[i];
                struct condpart *cp = amA(sizeof *cp);
                int tag = tags_first(ty, part->tags);
                if (tag == TyLet) {
                        cp->def = true;
                        cp->target = cexpr(ty, &part->items[0]);
                        cp->e = cexpr(ty, &part->items[1]);
                } else if (tag == TyAssign) {
                        cp->def = false;
                        cp->target = cexpr(ty, &part->items[0]);
                        cp->e = cexpr(ty, &part->items[1]);
                } else {
                        cp->def = false;
                        cp->target = NULL;
                        cp->e = cexpr(ty, part);
                }
                avP(parts, cp);
        }

        return parts;
}

Stmt *
cstmt(Ty *ty, Value *v)
{
        if (v == NULL || v->type == VALUE_NIL) {
                return NULL;
        }

        Stmt *s = amA0(sizeof *s);
        Stmt *src = source_lookup(ty, v->src);

        s->arena = GetArenaAlloc(ty);

        dont_printf("cstmt(): %s\n", value_show_color(ty, v));

        if (src == NULL && wrapped_type(ty, v) == VALUE_TUPLE) {
                Value *src_val = tuple_get(v, "src");
                if (src_val != NULL) {
                        src = source_lookup(ty, src_val->src);
                }
        }

        if (src != NULL) {
                s->start = src->start;
                s->end = src->end;
                s->mod = src->mod;
        } else {
                s->start = STATE.mstart;
                s->end = STATE.mend;
                s->mod = STATE.module;
        }

        if (v->type == VALUE_TAG) switch (v->tag) {
        case TyNull:
                goto Null;
        case TyContinue:
                goto Continue;
        case TyBreak:
                goto Break;
        }

        int tag = tags_first(ty, v->tags);

        switch (tag) {
        case TyStmt:
                return v->ptr;
        case TyLet:
        {
                Value *pub = tuple_get(v, "public");
                s->type = STATEMENT_DEFINITION;
                s->pub = pub != NULL && value_truthy(ty, pub);
                s->target = cexpr(ty, &v->items[0]);
                s->value = cexpr(ty, &v->items[1]);
                break;
        }
        case TyFuncDef:
        {
                Value f = *v;
                f.tags = tags_push(ty, 0, TyFunc);
                s->type = STATEMENT_FUNCTION_DEFINITION;
                s->value = cexpr(ty, &f);
                s->doc = s->value->doc;
                s->target = NewExpr(ty, EXPRESSION_IDENTIFIER);
                s->target->identifier = mkcstr(ty, t_(v, "name"));
                break;
        }
        case TyClass:
        {
                s->type = STATEMENT_CLASS_DEFINITION;
                s->class.name = mkcstr(ty, t_(v, "name"));
                s->class.doc = NULL;
                Value *super = tuple_get(v, "super");
                s->class.super = (super != NULL && super->type != VALUE_NIL) ? cexpr(ty, super) : NULL;
                Value *methods = tuple_get(v, "methods");
                Value *getters = tuple_get(v, "getters");
                Value *setters = tuple_get(v, "setters");
                Value *fields = tuple_get(v, "fields");
                Value *s_methods = tuple_get(v, "staticMethods");
                Value *s_getters = tuple_get(v, "staticGetters");
                Value *s_fields = tuple_get(v, "staticFields");
                if (methods != NULL) for (int i = 0; i < methods->array->count; ++i) {
                        if (tuple_get(v_(*methods->array, i), "name") == NULL) {
                                fail("class %s has an unnamed method", s->class.name);
                        }
                        avP(s->class.methods, cexpr(ty, &methods->array->items[i]));
                }
                if (getters != NULL) for (int i = 0; i < getters->array->count; ++i) {
                        avP(s->class.getters, cexpr(ty, &getters->array->items[i]));
                }
                if (setters != NULL) for (int i = 0; i < setters->array->count; ++i) {
                        if (tuple_get(v_(*setters->array, i), "name") == NULL) {
                                fail("class %s has an unnamed method", s->class.name);
                        }
                        avP(s->class.setters, cexpr(ty, &setters->array->items[i]));
                }
                if (fields != NULL) for (int i = 0; i < fields->array->count; ++i) {
                        avP(s->class.fields, cexpr(ty, &fields->array->items[i]));
                }
                if (s_methods != NULL) for (int i = 0; i < s_methods->array->count; ++i) {
                        avP(s->class.s_methods, cexpr(ty, &s_methods->array->items[i]));
                }
                if (s_getters != NULL) for (int i = 0; i < s_getters->array->count; ++i) {
                        avP(s->class.s_getters, cexpr(ty, &s_getters->array->items[i]));
                }
                if (s_fields != NULL) for (int i = 0; i < s_fields->array->count; ++i) {
                        avP(s->class.s_fields, cexpr(ty, &s_fields->array->items[i]));
                }
                break;
        }
        case TyIfNot:
                s->iff.neg =  true;
        if (0) {
        case TyIf:
                s->iff.neg = false;
        }
                s->type = STATEMENT_IF;
                s->iff.parts = cparts(ty, &v->items[0]);
                s->iff.then = cstmt(ty, &v->items[1]);
                if (v->count > 2 && v->items[2].type != VALUE_NIL) {
                        s->iff.otherwise = cstmt(ty, &v->items[2]);
                } else {
                        s->iff.otherwise = NULL;
                }
                break;
        case TyTry:
        {
                s->type = STATEMENT_TRY;

                v00(s->try.handlers);
                v00(s->try.patterns);

                Value *vBody = tuple_get(v, "body");
                Value *vCatches = tuple_get(v, "catches");
                Value *vFinally = tuple_get(v, "cleanup");

                if (vCatches->type != VALUE_ARRAY) {
                        fail("non-array `catches` in ty.Try construction: %s", value_show_color(ty, v));
                }

                s->try.s = cstmt(ty, vBody);
                s->try.finally = (vFinally == NULL || vFinally->type == VALUE_NIL) ? NULL : cstmt(ty, vFinally);

                for (int i = 0; i < vCatches->array->count; ++i) {
                        Value *catch = &vCatches->array->items[i];
                        if (catch->type != VALUE_TUPLE || catch->count != 2) {
                                fail_or(
                                        "invalid `catches` entry in ty.Try construction: %s",
                                        value_show_color(ty, catch)
                                ) {
                                        continue;
                                }
                        }
                        avP(s->try.patterns, cexpr(ty, &catch->items[0]));
                        avP(s->try.handlers, cstmt(ty, &catch->items[1]));
                }

                break;
        }
        case TyDefer:
                v->tags = tags_pop(ty, v->tags);
                s->type = STATEMENT_DEFER;
                s->expression = cexpr(ty, v);
                break;
        case TyMatch:
        {
                s->type = STATEMENT_MATCH;
                s->match.e = cexpr(ty, &v->items[0]);
                v00(s->match.patterns);
                v00(s->match.statements);
                v00(s->match.conds);
                Value *cases = &v->items[1];
                for (int i = 0; i < cases->array->count; ++i) {
                        Value *_case = &cases->array->items[i];
                        avP(s->match.patterns, cexpr(ty, &_case->items[0]));
                        avP(s->match.statements, cstmt(ty, &_case->items[1]));
                        avP(s->match.conds, NULL);

                        if ((*vvL(s->match.patterns))->type == EXPRESSION_LIST) {
                                (*vvL(s->match.patterns))->type = EXPRESSION_CHOICE_PATTERN;
                        }
                }
                break;
        }
        case TyWhileMatch:
        {
                s->type = STATEMENT_WHILE_MATCH;
                s->match.e = cexpr(ty, &v->items[0]);
                v00(s->match.patterns);
                v00(s->match.statements);
                v00(s->match.conds);
                Value *cases = &v->items[1];
                for (int i = 0; i < cases->array->count; ++i) {
                        Value *_case = &cases->array->items[i];
                        avP(s->match.patterns, cexpr(ty, &_case->items[0]));
                        avP(s->match.statements, cstmt(ty, &_case->items[1]));
                        avP(s->match.conds, NULL);
                }
                break;
        }
        case TyWhile:
                s->type = STATEMENT_WHILE;
                s->While.parts = cparts(ty, &v->items[0]);
                s->While.block = cstmt(ty, &v->items[1]);
                break;
        case TyFor:
                s->type = STATEMENT_FOR_LOOP;
                s->for_loop.init = cstmt(ty, &v->items[0]);
                s->for_loop.cond = cexpr(ty, &v->items[1]);
                s->for_loop.next = cexpr(ty, &v->items[2]);
                s->for_loop.body = cstmt(ty, &v->items[3]);
                break;
        case TyEach:
        {
                s->type = STATEMENT_EACH_LOOP;
                s->each.target = NewExpr(ty, EXPRESSION_LIST);

                Value *ps = tuple_get(v, "pattern");
                if (ps->type == VALUE_ARRAY) {
                        for (int i = 0; i < ps->array->count; ++i) {
                                avP(s->each.target->es, cexpr(ty, &ps->array->items[i]));
                        }
                } else {
                        avP(s->each.target->es, cexpr(ty, ps));
                }

                s->each.array = cexpr(ty, tuple_get(v, "iter"));
                s->each.body = cstmt(ty, tuple_get(v, "expr"));
                Value *cond = tuple_get(v, "cond");
                s->each.cond = (cond != NULL && cond->type != VALUE_NIL) ? cexpr(ty, cond) : NULL;
                Value *stop = tuple_get(v, "stop");
                s->each.stop = (stop != NULL && stop->type != VALUE_NIL) ? cexpr(ty, stop) : NULL;
                break;
        }
        case TyReturn:
        {
                s->type = STATEMENT_RETURN;
                v00(s->returns);
                if (wrapped_type(ty, v) == VALUE_TUPLE) {
                        for (int i = 0; i < v->count; ++i) {
                                avP(s->returns, cexpr(ty, &v->items[i]));
                        }
                } else {
                        Value v_ = unwrap(ty, v);
                        Expr *ret = cexpr(ty, &v_);
                        if (ret->type == EXPRESSION_LIST) {
                                avPn(s->returns, vv(ret->es), vN(ret->es));
                        } else {
                                avP(s->returns, ret);
                        }
                }
                break;
        }
        case TyBreak:
        Break:
        {
                s->type = STATEMENT_BREAK;
                if (v->type == VALUE_TAG) {
                        s->depth = 1;
                        s->expression = NULL;
                } else {
                        Value *expr = tuple_get(v, "value");
                        Value *depth = tuple_get(v, "depth");
                        s->depth = (depth == NULL || depth->type == VALUE_NIL) ? 1 : max(1, depth->integer);
                        s->expression = (expr == NULL || expr->type == VALUE_NIL) ? NULL : cexpr(ty, expr);
                }
                break;
        }
        case TyContinue:
        Continue:
        {
                s->type = STATEMENT_CONTINUE;
                if (v->type == VALUE_TAG) {
                        s->depth = 1;
                } else if ((v->type & ~VALUE_TAGGED) == VALUE_INTEGER) {
                        s->depth = max(1, v->integer);
                } else {
                        Value *depth = tuple_get(v, "depth");
                        s->depth = (depth == NULL || depth->type == VALUE_NIL) ? 1 : max(1, depth->integer);
                }
                break;
        }
        case TyBlock:
                s->type = STATEMENT_BLOCK;
                v00(s->statements);
                for (int i = 0; i < v->array->count; ++i) {
                        if (v->array->items[i].type == VALUE_NIL) {
                                fail("nil in block: %s", value_show_color(ty, v));
                        }
                        avP(s->statements, cstmt(ty, &v->array->items[i]));
                }
                break;
        case TyMulti:
                s->type = STATEMENT_MULTI;
                v00(s->statements);
                for (int i = 0; i < v->array->count; ++i) {
                        avP(s->statements, cstmt(ty, &v->array->items[i]));
                }
                break;
        case TyNull:
        Null:
                s->type = STATEMENT_NULL;
                break;
        default:
                s->type = STATEMENT_EXPRESSION;
                s->expression = cexpr(ty, v);
                if (s->expression == NULL) {
                        fail("cexpr() returned null pointer: %s", value_show_color(ty, v));
                }
                if (s->mod == NULL && s->expression->mod != NULL) {
                        s->mod = s->expression->mod;
                        s->start = s->expression->start;
                        s->end = s->expression->end;
                }
                break;
        }

        s->origin = STATE.origin;

        return s;
}

Expr *
cexpr(Ty *ty, Value *v)
{
        if (v == NULL || v->type == VALUE_NIL) {
                return NULL;
        }

        Expr *e = amA0(sizeof *e);
        Expr *src = source_lookup(ty, v->src);

        dont_printf("cexpr(): %s\n", value_show_color(ty, v));

        e->arena = GetArenaAlloc(ty);

        if (src == NULL && wrapped_type(ty, v) == VALUE_TUPLE) {
                Value *src_val = tuple_get(v, "src");
                if (src_val != NULL) {
                        src = source_lookup(ty, src_val->src);
                }
        }

        if (src != NULL) {
                e->start = src->start;
                e->end = src->end;
                e->mod = src->mod;
        } else {
                e->start = STATE.mstart;
                e->end = STATE.mend;
        }

        e->type = -1;

        if (v->type == VALUE_TAG) switch (v->tag) {
        case TyNil:
                e->type = EXPRESSION_NIL;
                return e;
        case TyNull:
        case TyBreak:
        case TyContinue:
                goto Statement;
        case TyAny:
                goto Any;
        }

        int tag = tags_first(ty, v->tags);

        switch (tag) {
        case 0:
                switch (v->type) {
                case VALUE_ARRAY:
                        e->type = EXPRESSION_LIST;
                        for (int i = 0; i < v->array->count; ++i) {
                                avP(e->es, cexpr(ty, &v->array->items[i]));
                        }
                        break;

                case VALUE_TYPE:
                        e->type = EXPRESSION_TYPE;
                        e->_type = v->ptr;
                        break;

                default:
                        goto Bad;
                }
                break;
        case TyExpr:
                return v->ptr;
        case TyType:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_TYPE;
                e->_type = type_from_ty(ty, &v_);
                break;
        }
        case TyValue:
        {
                Value *value = mrealloc(NULL, sizeof *value);

                *value = *v;

                value->tags = tags_pop(ty, value->tags);
                if (value->tags == 0) {
                        value->type &= ~VALUE_TAGGED;
                }

                e->type = EXPRESSION_VALUE;
                e->v = value;

                gc_immortalize(ty, value);

                break;
        }
        case TyInt:
                e->type = EXPRESSION_INTEGER;
                e->integer = v->integer;
                break;
        case TyFloat:
                e->type = EXPRESSION_REAL;
                e->real = v->real;
                break;
        case TyRegex:
                e->type = EXPRESSION_REGEX;
                e->regex = v->regex;
                break;
        case TyOperator:
                e->type = EXPRESSION_OPERATOR;
                e->op.id = mkcstr(ty, t_(v, 0));
                break;
        case TyId:
        {
                e->type = EXPRESSION_IDENTIFIER;
                e->identifier = mkcstr(ty, tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                Value *constraint = tuple_get(v, "constraint");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                e->constraint = (constraint != NULL && constraint->type != VALUE_NIL) ? cexpr(ty, constraint) : NULL;

                if (e->module == NULL && strcmp(e->identifier, "__line__") == 0) {
                        e->start = STATE.mstart;
                        e->end = STATE.mend;
                }

                break;
        }
        case TyPatternAlias:
        {
                e->type = EXPRESSION_ALIAS_PATTERN;
                e->identifier = mkcstr(ty, tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                Value *constraint = tuple_get(v, "constraint");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                e->constraint = (constraint != NULL && constraint->type != VALUE_NIL) ? cexpr(ty, constraint) : NULL;
                e->aliased = cexpr(ty, tuple_get(v, "pattern"));
                break;
        }
        case TyNotNil:
        {
                e->type = EXPRESSION_MATCH_NOT_NIL;
                e->identifier = mkcstr(ty, tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                break;
        }
        case TyAny:
        {
                if (v->count > 0) {
                        e->constraint = cexpr(ty, &v->items[0]);
                } else {
                        e->constraint = NULL;
                }
        Any:
                e->type = EXPRESSION_MATCH_ANY;
                e->identifier = "_";
                e->module = NULL;
                break;
        }
        case TyResource:
        {
                e->type = EXPRESSION_RESOURCE_BINDING;
                e->identifier = mkcstr(ty, tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                break;
        }
        case TySpread:
        {
                Value v_ = *v;
                v_.tags = tags_pop(ty, v_.tags);
                e->type = EXPRESSION_SPREAD;
                e->value = cexpr(ty, &v_);
                break;
        }
        case TySplat:
        {
                Value v_ = *v;
                v_.tags = tags_pop(ty, v_.tags);
                e->type = EXPRESSION_SPLAT;
                e->value = cexpr(ty, &v_);
                break;
        }
        case TyTagged:
        {
                e->type = EXPRESSION_TAG_APPLICATION;

                Expr *t = cexpr(ty, &v->items[0]);

                if (t->type == EXPRESSION_VALUE) {
                        if (t->v->type != VALUE_TAG) {
                                goto Bad;
                        }
                        e->identifier = (char *)EmptyString;
                        e->constraint = t;
                } else {
                        COPY_EXPR(e, t);
                }

                if (v->count < 2) {
                        goto Bad;
                } if (v->count == 2) {
                        e->tagged = cexpr(ty, &v->items[1]);
                } else {
                        e->tagged = NewExpr(ty, EXPRESSION_TUPLE);
                        for (int i = 1; i < v->count; ++i) {
                                avP(e->tagged->es, cexpr(ty, &v->items[i]));
                                avP(e->tagged->names, NULL);
                                avP(e->tagged->tconds, NULL);
                                avP(e->tagged->required, true);
                        }
                }

                break;
        }
        case TyString:
                e->type = EXPRESSION_STRING;
                e->string = mkcstr(ty, v);
                break;
        case TyLangString:
                e->lang = cexpr(ty, tget_nn(v, 0));
                v = tget_nn(v, 1);
        case TySpecialString:
        {
                e->type = EXPRESSION_SPECIAL_STRING;

                for (int i = 0; i < v->array->count; ++i) {
                        Value *x = &v->array->items[i];
                        if (x->type == VALUE_STRING) {
                                avP(e->strings, mkcstr(ty, x));
                        } else if (x->type == VALUE_TUPLE) {
                                avP(e->expressions, cexpr(ty, &x->items[0]));
                                avP(e->fmts, cexpr(ty, &x->items[1]));
                                avP(e->widths, (x->count > 2) ? x->items[2].integer : 0);
                                avP(e->fmtfs, cexpr(ty, tget_nn(x, 3)));
                        } else {
                                avP(e->expressions, cexpr(ty, x));
                                avP(e->fmts, NULL);
                                avP(e->widths, 0);
                                avP(e->fmtfs, NULL);
                        }
                }

                if (v->array->count == 0 || vvL(*v->array)->type != VALUE_STRING) {
                        avP(e->strings, "");
                }

                break;
        }
        case TyArray:
        {
                e->type = EXPRESSION_ARRAY;

                for (int i = 0; i < vN(*v->array); ++i) {
                        Value *entry    = v_(*v->array, i);

                        Value *item     = tuple_get(entry, "item");
                        Value *optional = tuple_get(entry, "optional");
                        Value *cond     = tuple_get(entry, "cond");

                        if (item == NULL) {
                                goto Bad;
                        }

                        avP(e->elements, cexpr(ty, tuple_get(entry, "item")));
                        avP(e->optional, optional != NULL ? optional->boolean : false);
                        avP(e->aconds, (cond != NULL && cond->type != VALUE_NIL) ? cexpr(ty, cond) : NULL);
                }

                break;
        }
        case TyUnion:
        {
                e->type = EXPRESSION_TYPE_UNION;

                for (int i = 0; i < vN(*v->array); ++i) {
                        Value *alt = v_(*v->array, i);
                        avP(e->es, cexpr(ty, alt));
                }

                break;
        }
        case TyRecord:
        {
                e->type = EXPRESSION_TUPLE;

                Value elems = unwrap(ty, v);

                if (elems.type != VALUE_ARRAY) {
                        goto Bad;
                }

                for (int i = 0; i < vN(*elems.array); ++i) {
                        Value *entry = v_(*elems.array, i);

                        Value *item     = tuple_get(entry, "item");
                        Value *name     = tget_t(entry, "name", VALUE_STRING);
                        Value *optional = tget_t(entry, "optional", VALUE_BOOLEAN);
                        Value *cond     = tget_nn(entry, "cond");

                        if (item == NULL) {
                                goto Bad;
                        }

                        avP(e->es, cexpr(ty, item));
                        avP(e->names, (name != NULL) ? mkcstr(ty, name) : NULL);
                        avP(e->required, optional != NULL ? !optional->boolean : true);
                        avP(e->tconds, cexpr(ty, cond));
                }

                break;
        }
        case TyChoicePattern:
        {
                e->type = EXPRESSION_CHOICE_PATTERN;

                for (int i = 0; i < v->array->count; ++i) {
                        Value *entry = &v->array->items[i];
                        avP(e->es, cexpr(ty, entry));
                        avP(e->names, NULL);
                        avP(e->required, true);
                        avP(e->tconds, NULL);
                }

                break;
        }
        case TyDict:
        {
                e->type = EXPRESSION_DICT;
                e->dtmp = NULL;

                Value *items = tuple_get(v, "items");
                Value *dflt = tuple_get(v, "default");

                e->dflt = (dflt != NULL && dflt->type != VALUE_NIL) ? cexpr(ty, dflt) : NULL;

                for (int i = 0; i < items->array->count; ++i) {
                        avP(e->keys, cexpr(ty, &v__(items->array->items[i], 0)));
                        avP(e->values, cexpr(ty, &v__(items->array->items[i], 1)));
                }

                break;
        }
        case TyCall:
        {
                e->type = EXPRESSION_FUNCTION_CALL;

                Value *func = tuple_get(v, "func");
                e->function = cexpr(ty, func);

                Value *args = tuple_get(v, "args");

                for (int i = 0; i < args->array->count; ++i) {
                        Value *arg = &args->array->items[i];
                        Value *name = tuple_get(arg, "name");
                        Value *cond = tuple_get(arg, "cond");
                        if (cond != NULL && cond->type == VALUE_NIL) {
                                cond = NULL;
                        }
                        if (name == NULL || name->type == VALUE_NIL) {
                                avP(e->args, cexpr(ty, tuple_get(arg, "arg")));
                                avP(e->fconds, cond != NULL ? cexpr(ty, cond) : NULL);
                        } else {
                                avP(e->kwargs, cexpr(ty, tuple_get(arg, "arg")));
                                avP(e->kws, mkcstr(ty, name));
                                avP(e->fkwconds, cond != NULL ? cexpr(ty, cond) : NULL);
                        }
                }

                break;
        }
        case TyMethodCall:
        case TyTryMethodCall:
        case TyDynMethodCall:
        case TyTryDynMethodCall:
        {
                Value *method = tuple_get(v, "method");

                switch (tag) {
                case TyTryMethodCall:
                        e->maybe = true;
                case TyMethodCall:
                        e->type = EXPRESSION_METHOD_CALL;
                        e->method = NewExpr(ty, EXPRESSION_IDENTIFIER);
                        e->method->identifier = mkcstr(ty, method);
                        break;

                case TyTryDynMethodCall:
                        e->maybe = true;
                case TyDynMethodCall:
                        e->type = EXPRESSION_DYN_METHOD_CALL;
                        e->method = cexpr(ty, method);
                        break;

                }

                Value *object = tuple_get(v, "object");
                e->object = cexpr(ty, object);

                Value *args = tuple_get(v, "args");

                for (int i = 0; i < args->array->count; ++i) {
                        Value *arg = &args->array->items[i];
                        Value *cond = tget_nn(arg, "cond");
                        Value *name = tget_t(arg, "name", VALUE_STRING);

                        if (name == NULL) {
                                avP(e->method_args, cexpr(ty, tuple_get(arg, "arg")));
                                avP(e->mconds, cond != NULL ? cexpr(ty, cond) : NULL);
                        } else {
                                avP(e->method_kwargs, cexpr(ty, tuple_get(arg, "arg")));
                                avP(e->method_kws, mkcstr(ty, name));
                        }
                }
                break;
        }
        case TyGenerator:
        {
                Value v_ = *v;
                v_.tags = tags_pop(ty, v_.tags);
                e->type = EXPRESSION_GENERATOR;
                e->ikwargs = -1;
                e->rest = -1;
                e->class = -1;
                e->ftype = FT_GEN;
                e->body = cstmt(ty, &v_);
                break;
        }
        case TyFunc:
        case TyImplicitFunc:
        {
                e->type = tag == TyFunc ? EXPRESSION_FUNCTION : EXPRESSION_IMPLICIT_FUNCTION;
                e->ikwargs = -1;
                e->rest = -1;
                e->class = -1;
                e->ftype = FT_NONE;
                Value *name = tuple_get(v, "name");
                Value *params = tuple_get(v, "params");
                Value *rt = tuple_get(v, "rt");
                Value *decorators = tuple_get(v, "decorators");
                Value *doc = tuple_get(v, "doc");
                Value *proto = tuple_get(v, "proto");
                e->name = (name != NULL && name->type != VALUE_NIL) ? mkcstr(ty, name) : NULL;
                e->doc = (doc != NULL && doc->type != VALUE_NIL) ? mkcstr(ty, doc) : NULL;
                e->proto = (proto != NULL && proto->type != VALUE_NIL) ? mkcstr(ty, proto) : NULL;
                e->return_type = (rt != NULL && rt->type != VALUE_NIL) ? cexpr(ty, rt) : NULL;
                if (decorators != NULL && decorators->type != VALUE_NIL) {
                        for (int i = 0; i < decorators->array->count; ++i) {
                                avP(e->decorators, cexpr(ty, &decorators->array->items[i]));
                        }
                }
                for (int i = 0; i < params->array->count; ++i) {
                        Value *p = &params->array->items[i];
                        switch (tags_first(ty, p->tags)) {
                        case TyParam:
                        {
                                avP(e->params, mkcstr(ty, tuple_get(p, "name")));
                                Value *c = tuple_get(p, "constraint");
                                Value *d = tuple_get(p, "default");
                                avP(e->constraints, (c != NULL && c->type != VALUE_NIL) ? cexpr(ty, c) : NULL);
                                avP(e->dflts, (d != NULL && d->type != VALUE_NIL) ? cexpr(ty, d) : NULL);
                                break;
                        }
                        case TyGather:
                                avP(e->params, mkcstr(ty, p));
                                avP(e->constraints, NewExpr(ty, EXPRESSION_MATCH_ANY));
                                avP(e->dflts, NULL);
                                e->rest = i;
                                break;
                        case TyKwargs:
                                avP(e->params, mkcstr(ty, p));
                                avP(e->constraints, NewExpr(ty, EXPRESSION_MATCH_ANY));
                                avP(e->dflts, NULL);
                                e->ikwargs = i;
                                break;
                        }
                }
                e->body = cstmt(ty, tuple_get(v, "body"));
                break;
        }
        case TyArrayCompr:
        {
                Value *pattern = tuple_get(v, "pattern");
                Value *iter = tuple_get(v, "iter");
                Value *cond = tuple_get(v, "cond");
                Value *where = tget_nn(v, "where");
                Value *items = tuple_get(v, "items");

                if (pattern == NULL || iter == NULL)
                        goto Bad;

                e->type = EXPRESSION_ARRAY_COMPR;
                e->compr.pattern = cexpr(ty, pattern);
                e->compr.iter = cexpr(ty, iter);
                e->compr.cond = (cond == NULL || cond->type == VALUE_NIL) ? NULL : cexpr(ty, cond);
                e->compr.where = (where == NULL) ? NULL : cstmt(ty, where);

                for (int i = 0; i < items->array->count; ++i) {
                        Value *entry = &items->array->items[i];
                        Value *optional = tuple_get(entry, "optional");
                        Value *cond = tuple_get(entry, "cond");
                        avP(e->elements, cexpr(ty, tuple_get(entry, "item")));
                        avP(e->optional, optional != NULL ? optional->boolean : false);
                        avP(e->aconds, (cond != NULL && cond->type != VALUE_NIL) ? cexpr(ty, cond) : NULL);
                }

                break;
        }
        case TyDictCompr:
        {
                Value *pattern = tuple_get(v, "pattern");
                Value *iter = tuple_get(v, "iter");
                Value *cond = tget_nn(v, "cond");
                Value *where = tget_nn(v, "where");
                Value *dflt = tget_nn(v, "default");
                Value *items = tuple_get(v, "items");

                if (pattern == NULL || iter == NULL)
                        goto Bad;

                e->type = EXPRESSION_DICT_COMPR;
                e->dflt = cexpr(ty, dflt);
                e->dcompr.pattern = cexpr(ty, pattern);
                e->dcompr.iter = cexpr(ty, iter);
                e->dcompr.cond = cexpr(ty, cond);
                e->dcompr.where = cstmt(ty, where);

                for (int i = 0; i < vN(*items->array); ++i) {
                        Value entry = unwrap(ty, v_(*items->array, i));
                        Value *key = tget_nn(&entry, 0);
                        Value *value = tget_nn(&entry, 1);
                        avP(e->keys, cexpr(ty, key));
                        avP(e->values, cexpr(ty, value));
                }

                break;
        }
        case TyTryMemberAccess:
                e->maybe = true;
        case TyMemberAccess:
                if (v->items[0].type == VALUE_NIL) {
                        e->type = EXPRESSION_SELF_ACCESS;
                } else {
                        e->type = EXPRESSION_MEMBER_ACCESS;
                        e->object = cexpr(ty, &v->items[0]);
                        if (e->object == NULL) {
                                goto Bad;
                        }
                }
                e->member = NewExpr(ty, EXPRESSION_IDENTIFIER);
                e->member->identifier = mkcstr(ty, &v->items[1]);
                break;
        case TyDynMemberAccess:
                e->type = EXPRESSION_DYN_MEMBER_ACCESS;
                e->object = cexpr(ty, &v->items[0]);
                e->member = cexpr(ty, &v->items[1]);
                break;
        case TyTryDynMemberAccess:
                e->type = EXPRESSION_DYN_MEMBER_ACCESS;
                e->maybe = true;
                e->object = cexpr(ty, &v->items[0]);
                e->member = cexpr(ty, &v->items[1]);
                break;
        case TySubscript:
                e->type = EXPRESSION_SUBSCRIPT;
                e->container = cexpr(ty, &v->items[0]);
                e->subscript = cexpr(ty, &v->items[1]);
                break;
        case TySlice:
                e->type = EXPRESSION_SLICE;
                e->slice.e = cexpr(ty, &v->items[0]);
                e->slice.i = cexpr(ty, &v->items[1]);
                e->slice.j = cexpr(ty, &v->items[2]);
                e->slice.k = cexpr(ty, &v->items[3]);
                break;
        case TyEval:
        {
                Value v_ = *v;
                v_.tags = tags_pop(ty, v_.tags);
                e->type = EXPRESSION_EVAL;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyYield:
                e->type = EXPRESSION_YIELD;
                v00(e->es);
                if ((v->type & ~VALUE_TAGGED) == VALUE_ARRAY) {
                        for (int i = 0; i < v->array->count; ++i) {
                                avP(e->es, cexpr(ty, &v->array->items[i]));
                        }
                } else {
                        Value v_ = *v;
                        v_.tags = tags_pop(ty, v_.tags);
                        avP(e->es, cexpr(ty, &v_));
                }
                break;
        case TyThrow:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_THROW;
                e->throw = cexpr(ty, &v_);
                break;
        }
        case TyWith:
        {
                Value *lets = &v->items[0];
                statement_vector defs = {0};

                for (int i = 0; i < lets->array->count; ++i) {
                        avP(defs, cstmt(ty, &lets->array->items[i]));
                }

                make_with(ty, e, defs, cstmt(ty, &v->items[1]));

                break;
        }
        case TyCast:
                e->type = EXPRESSION_CAST;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyCond:
                e->type = EXPRESSION_CONDITIONAL;
                e->cond = cexpr(ty, &v->items[0]);
                e->then = cexpr(ty, &v->items[1]);
                e->otherwise = cexpr(ty, &v->items[2]);
                break;
        case TyBool:
                e->type = EXPRESSION_BOOLEAN;
                e->boolean = v->boolean;
                break;
        case TyAssign:
                e->type = EXPRESSION_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutAdd:
                e->type = EXPRESSION_PLUS_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutSub:
                e->type = EXPRESSION_MINUS_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutMul:
                e->type = EXPRESSION_STAR_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutDiv:
                e->type = EXPRESSION_DIV_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutMod:
                e->type = EXPRESSION_MOD_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutAnd:
                e->type = EXPRESSION_AND_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutOr:
                e->type = EXPRESSION_OR_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutXor:
                e->type = EXPRESSION_XOR_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutShl:
                e->type = EXPRESSION_SHL_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyMutShr:
                e->type = EXPRESSION_SHR_EQ;
                e->target = cexpr(ty, &v->items[0]);
                e->value = cexpr(ty, &v->items[1]);
                break;
        case TyRange:
                e->type = EXPRESSION_DOT_DOT;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyIncRange:
                e->type = EXPRESSION_DOT_DOT_DOT;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyView:
                e->type = EXPRESSION_VIEW_PATTERN;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyNotNilView:
                e->type = EXPRESSION_NOT_NIL_VIEW_PATTERN;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyWtf:
                e->type = EXPRESSION_WTF;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyAdd:
                e->type = EXPRESSION_PLUS;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TySub:
                e->type = EXPRESSION_MINUS;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyMod:
                e->type = EXPRESSION_PERCENT;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyDiv:
                e->type = EXPRESSION_DIV;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyMul:
                e->type = EXPRESSION_STAR;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyXor:
                e->type = EXPRESSION_XOR;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyShl:
                e->type = EXPRESSION_SHL;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyShr:
                e->type = EXPRESSION_SHR;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyEq:
                e->type = EXPRESSION_DBL_EQ;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyNotEq:
                e->type = EXPRESSION_NOT_EQ;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyGT:
                e->type = EXPRESSION_GT;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyGEQ:
                e->type = EXPRESSION_GEQ;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyLT:
                e->type = EXPRESSION_LT;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyLEQ:
                e->type = EXPRESSION_LEQ;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyCmp:
                e->type = EXPRESSION_CMP;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyMatches:
                e->type = EXPRESSION_CHECK_MATCH;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyIn:
                e->type = EXPRESSION_IN;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyNotIn:
                e->type = EXPRESSION_NOT_IN;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyOr:
                e->type = EXPRESSION_OR;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyAnd:
                e->type = EXPRESSION_AND;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyKwAnd:
                e->type = EXPRESSION_KW_AND;
                e->left = cexpr(ty, &v->items[0]);
                e->p_cond = cparts(ty, &v->items[1]);
                break;
        case TyBitAnd:
                e->type = EXPRESSION_BIT_AND;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyBitOr:
                e->type = EXPRESSION_BIT_OR;
                e->left = cexpr(ty, &v->items[0]);
                e->right = cexpr(ty, &v->items[1]);
                break;
        case TyUserOp:
                e->type = EXPRESSION_USER_OP;
                e->op_name = mkcstr(ty, &v->items[0]);
                e->left = cexpr(ty, &v->items[1]);
                e->right = cexpr(ty, &v->items[2]);
                break;
        case TyTypeOf:
        {
                Value v_ = *v;
                v_.tags = tags_pop(ty, v_.tags);
                e->type = EXPRESSION_TYPE_OF;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyCount:
        {
                Value v_ = *v;
                v_.tags = tags_pop(ty, v_.tags);
                e->type = EXPRESSION_PREFIX_HASH;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyNot:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_PREFIX_BANG;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyNeg:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_PREFIX_MINUS;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyPreInc:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_PREFIX_INC;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyPostInc:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_POSTFIX_INC;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyPreDec:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_PREFIX_DEC;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyPostDec:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_POSTFIX_DEC;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyQuestion:
        {
                Value v_ = unwrap(ty, v);
                e->type = EXPRESSION_PREFIX_QUESTION;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyTagPattern:
        {
                e->type = EXPRESSION_TAG_PATTERN;
                e->identifier = mkcstr(ty, &v->items[0]);
                e->module = NULL;
                e->constraint = NULL;
                e->tagged = cexpr(ty, &v->items[1]);
                break;
        }
        case TyCompileTime:
        {
                Value v_ = *v;
                v_.tags = tags_pop(ty, v_.tags);
                e->type = EXPRESSION_COMPILE_TIME;
                e->operand = cexpr(ty, &v_);
                break;
        }
        case TyIfDef:
        {
                e->type = EXPRESSION_IFDEF;
                e->identifier = mkcstr(ty, t_(v, "name"));
                Value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                break;
        }
        case TyDefined:
        {
                e->type = EXPRESSION_DEFINED;
                e->identifier = mkcstr(ty, t_(v, "name"));
                Value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                break;
        }
        case TyLet:
        case TyMatch:
        case TyTry:
        case TyEach:
        case TyFor:
        case TyWhile:
        case TyWhileMatch:
        case TyIf:
        case TyIfNot:
        case TyStmt:
        case TyBlock:
        case TyNull:
        case TyMulti:
        case TyFuncDef:
        case TyClass:
        case TyBreak:
        case TyContinue:
        case TyReturn:
        Statement:
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(ty, v);
                if (e->mod == NULL && e->statement->mod != NULL) {
                        e->mod = e->statement->mod;
                        e->start = e->statement->start;
                        e->end = e->statement->end;
                }
                break;
        default:
        Bad:
                fail("invalid value passed to cexpr(): %s", VSC(v));
        }

        Scope *scope = STATE.macro_scope == NULL
                     ? STATE.global
                     : STATE.macro_scope;

        fixup_access(ty, scope, e, false);
        e->origin = STATE.origin;

        return e;
}

Value
CToTyExpr(Ty *ty, Expr *e)
{
        GC_STOP();

        if (TY_CATCH_ERROR()) {
                GC_RESUME();
                return NONE;
        }

        Value v = tyexpr(ty, e);

        GC_RESUME();
        TY_CATCH_END();

        return v;
}

Value
CToTyStmt(Ty *ty, Stmt *s)
{
        GC_STOP();

        if (TY_CATCH_ERROR()) {
                GC_RESUME();
                return NONE;
        }

        Value v = tystmt(ty, s);

        GC_RESUME();
        TY_CATCH_END();

        return v;
}

Expr *
TyToCExpr(Ty *ty, Value *v)
{
        GC_STOP();

        if (TY_CATCH_ERROR()) {
                GC_RESUME();
                return NULL;
        }

        Expr *e = cexpr(ty, v);

        GC_RESUME();
        TY_CATCH_END();

        return e;
}

Value
tyeval(Ty *ty, Expr *e)
{
        if (TY_CATCH_ERROR()) {
                return NONE;
        }

        if (e->xscope == NULL) {
                symbolize_expression(
                        ty,
                        (
                                STATE.macro_scope != NULL
                              ? STATE.macro_scope
                              : STATE.global
                        ),
                        e
                );
        }

        byte_vector code_save = STATE.code;
        v00(STATE.code);

        location_vector locs_save = STATE.expression_locations;
        v00(STATE.expression_locations);

        EE(e);
        INSN(HALT);

        TY_CATCH_END();

        usize n_location_lists = vN(location_lists);

        add_location_info(ty);

        EVAL_DEPTH += 1;
        Value v = vm_try_exec(ty, vv(STATE.code));
        EVAL_DEPTH -= 1;

        STATE.code = code_save;
        STATE.expression_locations = locs_save;

        vN(location_lists) = n_location_lists;

        return v;
}

Value
compiler_eval(
        Ty *ty,
        Expr *e
)
{
        symbolize_expression(ty, STATE.global, e);

        byte_vector code_save = STATE.code;
        v00(STATE.code);

        add_location_info(ty);
        v00(STATE.expression_locations);

        ProgramAnnotation annotation = STATE.annotation;
        STATE.annotation = (ProgramAnnotation) {0};

        EE(e);
        INSN(HALT);

        v00(STATE.expression_locations);

        vm_exec(ty, vv(STATE.code));

        STATE.code = code_save;
        STATE.annotation = annotation;
        v00(STATE.expression_locations);

        Value v = *vm_get(ty, 0);
        vmX();

        return v;
}

Expr *
typarse(
        Ty *ty,
        Expr *e,
        Expr *self,
        Location const *start,
        Location const *end
)
{
        symbolize_expression(ty, STATE.global, e);
        DefinePending(ty);

        byte_vector code_save = STATE.code;
        v00(STATE.code);

        add_location_info(ty);
        v00(STATE.expression_locations);

        ProgramAnnotation annotation = STATE.annotation;
        STATE.annotation = (ProgramAnnotation) {0};

        EE(e);
        INSN(HALT);

        v00(STATE.expression_locations);

        vm_exec(ty, vv(STATE.code));

        STATE.code = code_save;
        STATE.annotation = annotation;
        v00(STATE.expression_locations);

        Value m = *vm_get(ty, 0);

        void *ctx = PushInfo(ty, NULL, "invoking macro %s", name_of(&m));

        Scope *macro_scope_save = STATE.macro_scope;
        STATE.macro_scope = STATE.global;

        Location const mstart = STATE.mstart;
        Location const mend = STATE.mend;
        STATE.mstart = *start;
        STATE.mend = *end;

        Value vSelf = (self == NULL) ? NIL : tyexpr(ty, self);
        Value expr;

        vmP(&vSelf);
        expr = vmC(&m, 1);
        vmP(&expr);

        STATE.macro_scope = macro_scope_save;

        Expr *e_ = cexpr(ty, &expr);

        STATE.mstart = mstart;
        STATE.mend = mend;

        // Take `m` and `expr` off the stack
        vmX();
        vmX();

        RestoreContext(ty, ctx);

        return e_;
}

static void
AddClassFields(
        Ty *ty,
        Class *c,
        Scope *scope,
        expression_vector const *fields,
        add_field_to_class_fn *add,
        u32 extra_flags
)
{
        SCRATCH_SAVE();

        char *scratch = smA(512);

        for (int i = 0; i < vN(*fields); ++i) {
                Expr *field = v__(*fields, i);

                switch (field->type) {
                case EXPRESSION_IDENTIFIER:
                case EXPRESSION_EQ:
                        break;

                default:
                        fail(
                                "unexpected expression used as field declaration: %s",
                                ExpressionTypeName(field)
                        );
                }

                Expr *ident = FieldIdentifier(field);
                char const *name = ident->identifier;
                char const *private_name = GetPrivateName(name, c->i, scratch, 512);

                i32 id = M_ID(private_name);

                (*add)(ty, c, id, field->constraint, (field == ident) ? NULL : field->value);

                ident->symbol = addsymbol(ty, scope, name);
                ident->symbol->flags |= SYM_MEMBER;
                ident->symbol->flags |= extra_flags;
                ident->symbol->member = id;
        }

        SCRATCH_RESTORE();
}

static void
AddClassTraits(Ty *ty, ClassDefinition const *def)
{
        for (int i = 0; i < vN(def->traits); ++i) {
                int t = ResolveClassSpec(ty, v__(def->traits, i));
                class_implement_trait(ty, def->symbol, t);
        }
}

static void
ResolveFieldTypes(Ty *ty, Scope *scope, expression_vector const *fields)
{
        for (int i = 0; i < vN(*fields); ++i) {
                Expr *f = FieldIdentifier(v__(*fields, i));
                if (f->constraint != NULL) {
                        WITH_CTX(TYPE) {
                                symbolize_expression(ty, scope, f->constraint);
                                f->_type = type_fixed(ty, type_resolve(ty, f->constraint));
                                f->symbol->type = f->_type;
                                f->symbol->flags |= SYM_FIXED;
                                SET_TYPE_SRC(f);
                        }
                }
        }
}

void
define_tag(Ty *ty, Stmt *s)
{
        Scope *scope = GetNamespace(ty, s->ns);

        if (scope_locally_defined(ty, scope, s->tag.name)) {
                fail("redeclaration of tag: %s", s->tag.name);
        }

        s->tag.scope = scope_new(ty, s->tag.name, scope, false);

        for (int i = 0; i < vN(s->tag.type_params); ++i) {
                Expr *t0 = v__(s->tag.type_params, i);
                t0->symbol = scope_add_type_var(ty, s->tag.scope, t0->identifier);
                symbolize_expression(ty, s->tag.scope, t0->constraint);
        }

        Symbol *sym = addsymbol(ty, scope, s->tag.name);
        sym->flags |= SYM_CONST;
        sym->tag = tags_new(ty, s->tag.name);
        sym->doc = s->tag.doc;
        s->tag.symbol = sym->tag;
        s->tag.var = sym;

        if (s->tag.super != NULL) {
                symbolize_expression(ty, s->tag.scope, s->tag.super);
#if 0
                Type *t0 = type_resolve(ty, s->tag.super);

                if (
                        t0 == NULL
                     || (
                                t0->type != TYPE_TAG
                             && t0->type != TYPE_OBJECT
                        )
                ) {
                        fail("attempt to extend non-tag");
                }

                Class *super = t0->class;

                class_set_super(ty, s->tag.symbol, super->i);

                for (int i = 0; i < vN(s->tag.methods); ++i) {
                        Expr *m = v__(s->tag.methods, i);
                        if (m->return_type == NULL) {
                                Value *v = class_method(ty, super->i, m->name);
                                if (v != NULL && v->type == VALUE_PTR) {
                                        m->return_type = ((Expr *)v->ptr)->return_type;
                                }
                        }
                }

                tags_set_class(ty, sym->tag, super);
                sym->type = type_tag(ty, super);
#endif
        } else {
                Class *class = class_get(ty, class_new(ty, s));
                tags_set_class(ty, sym->tag, class);
                sym->type = type_tag(ty, class, sym->tag);

        }

        for (int i = 0; i < vN(s->tag.methods); ++i) {
                // :^)
                v__(s->tag.methods, i)->class = -3;
        }

        for (int i = 0; i < vN(s->tag.s_methods); ++i) {
                // :^)
                v__(s->tag.s_methods, i)->class = -3;
        }
}

void
define_type(Ty *ty, Stmt *s, Scope *scope)
{
        if (s->class.var != NULL) {
                return;
        }

        DefinePending(ty);

        if (scope == NULL) {
                scope = GetNamespace(ty, s->ns);
        }

        s->class.scope = scope_new(ty, s->class.name, scope, false);

        void *ctx = PushContext(ty, s);

        for (int i = 0; i < vN(s->class.type_params); ++i) {
                Expr *t0 = v__(s->class.type_params, i);
                t0->symbol = scope_add_type_var(ty, s->class.scope, t0->identifier);
                symbolize_expression(ty, s->class.scope, t0->constraint);
        }

        Symbol *sym = scope_local_lookup(ty, scope, s->class.name);

        if (sym == NULL) {
                sym = scope_add_type_var(ty, scope, s->class.name);
        } else if (!ModuleIsReloading(STATE.module)) {
                fail(
                        "redeclaration of %s%s%s%s",
                        TERM(1),
                        TERM(34),
                        s->class.name,
                        TERM(0)
                );
        }

        sym->doc = s->class.doc;
        sym->loc = s->class.loc;
        sym->flags |= SYM_CONST;
        sym->flags |= SYM_PUBLIC * s->class.pub;
        s->class.symbol = sym->class;
        s->class.var = sym;

        WITH_CTX(TYPE) WITH_PERMISSIVE_SCOPE {
                symbolize_expression(ty, s->class.scope, s->class.type);
        }

        type_alias(ty, sym, s);

        RestoreContext(ty, ctx);
}

void
define_class(Ty *ty, Stmt *s)
{
        void *ctx = PushContext(ty, s);

        Scope *scope = GetNamespace(ty, s->ns);

        s->class.scope = scope_new(ty, s->class.name, scope, false);

        for (int i = 0; i < vN(s->class.type_params); ++i) {
                Expr *t0 = v__(s->class.type_params, i);
                t0->symbol = scope_add_type_var(ty, s->class.scope, t0->identifier);
                symbolize_expression(ty, s->class.scope, t0->constraint);
        }

        Symbol *sym = scope_local_lookup(ty, scope, s->class.name);

        if (sym == NULL) {
                sym = addsymbol(ty, scope, s->class.name);
                sym->class = s->class.is_trait
                           ? trait_new(ty, s)
                           : class_new(ty, s);
        } else if (
                (sym->class < CLASS_BUILTIN_END)
             && (sym->class != -1)
        ) {
                class_builtin(ty, sym->class, s);
        } else {
                fail(
                        "redeclaration of class %s%s%s%s%s",
                        TERM(1),
                        TERM(34),
                        s->class.name,
                        TERM(22),
                        TERM(39)
                );
        }

        Class *class = class_get(ty, sym->class);
        ClassDefinition *cd = &s->class;

        sym->flags |= SYM_CONST;
        sym->doc = cd->doc;
        sym->loc = cd->loc;
        sym->mod = s->mod;
        sym->flags |= SYM_CONST;
        cd->symbol = sym->class;
        cd->var = sym;

        sym->type = class->type;

        XLOG(
                "%s================%s DEFINE CLASS: %s :: %s %s==========================%s",
                TERM(91),
                TERM(0),
                cd->name,
                type_show(ty, class->object_type),
                TERM(91),
                TERM(0)
        );

        for (int i = 0; i < vN(cd->traits); ++i) {
                Expr *trait0 = v__(cd->traits, i);
                TryResolveExpr(ty, cd->scope, trait0);
        }

        char scratch[512];
        char const *name;

        int keep = 0;
        for (int i = 0; i < vN(cd->methods); ++i) {
                Expr *m = v__(cd->methods, i);
                if (contains(OperatorCharset, *m->name) && vN(m->params) > 0) {
                        Expr *this;
                        if (CheckTypes) {
                                this = NewExpr(ty, EXPRESSION_TYPE);
                                this->_type = class->object_type;
                        } else {
                                this = NewExpr(ty, EXPRESSION_IDENTIFIER);
                                this->identifier = cd->name;
                                symbolize_expression(ty, cd->scope, this);
                        }

                        Expr *copy = aclone(m);

                        m->body = NULL;

                        copy->class = sym->class;
                        copy->mtype = MT_2OP;

                        avC(copy->params);
                        avC(copy->param_symbols);
                        avC(copy->constraints);
                        avC(copy->dflts);
                        avC(copy->type_params);

                        avI(copy->params, "self", 0);
                        avI(copy->dflts, NULL, 0);
                        avI(copy->constraints, this, 0);
                        avPv(copy->type_params, cd->type_params);

                        Stmt *def = NewStmt(ty, STATEMENT_OPERATOR_DEFINITION);
                        def->target = NewExpr(ty, EXPRESSION_IDENTIFIER);
                        def->target->identifier = copy->name;
                        def->value = copy;

                        WITH_STATE(meth, copy) {
                                define_operator(ty, cd->scope, def);
                        }

                        if (copy->body != NULL) {
                                avP(STATE.class_ops, def);
                        }
                } else {
                        m->class = sym->class;
                        m->_type = UNKNOWN_TYPE;

                        name = GetPrivateName(m->name, sym->class, scratch, sizeof scratch);
                        class_add_method(ty, sym->class, name, REF(NewZero()));

                        m->fn_symbol = addsymbol(ty, cd->scope, m->name);
                        m->fn_symbol->flags |= SYM_MEMBER;
                        m->fn_symbol->member = M_ID(name);

                        *v_(cd->methods, keep++) = m;
                }
        }

        // Drop binary ops
        vN(cd->methods) = keep;

        for (int i = 0; i < vN(cd->s_methods); ++i) {
                Expr *m = v__(cd->s_methods, i);
                m->_type = UNKNOWN_TYPE;
                m->class = sym->class;
                name = GetPrivateName(m->name, sym->class, scratch, sizeof scratch);
                class_add_static(ty, sym->class, name, REF(NewZero()));

                m->fn_symbol = addsymbol(ty, cd->scope, m->name);
                m->fn_symbol->flags |= SYM_MEMBER;
                m->fn_symbol->flags |= SYM_STATIC;
                m->fn_symbol->member = M_ID(name);
        }

        for (int i = 0; i < vN(cd->s_getters); ++i) {
                Expr *m = v__(cd->s_getters, i);
                m->_type = UNKNOWN_TYPE;
                m->class = sym->class;
                name = GetPrivateName(m->name, sym->class, scratch, sizeof scratch);
                class_add_s_getter(ty, sym->class, name, REF(NewZero()));

                m->fn_symbol = addsymbol(ty, cd->scope, m->name);
                m->fn_symbol->flags |= SYM_MEMBER;
                m->fn_symbol->flags |= SYM_STATIC;
                m->fn_symbol->member = M_ID(name);
        }

        for (int i = 0; i < vN(cd->getters); ++i) {
                Expr *m = v__(cd->getters, i);
                m->_type = UNKNOWN_TYPE;
                m->class = sym->class;
                name = GetPrivateName(m->name, sym->class, scratch, sizeof scratch);
                class_add_getter(ty, sym->class, name, REF(NewZero()));

                m->fn_symbol = addsymbol(ty, cd->scope, m->name);
                m->fn_symbol->flags |= SYM_MEMBER;
                m->fn_symbol->flags |= SYM_PROPERTY;
                m->fn_symbol->member = M_ID(name);
        }

        for (int i = 0; i < vN(cd->setters); ++i) {
                Expr *m = v__(cd->setters, i);
                m->_type = UNKNOWN_TYPE;
                m->class = sym->class;
                name = GetPrivateName(m->name, sym->class, scratch, sizeof scratch);
                class_add_setter(ty, sym->class, name, REF(NewZero()));

                m->fn_symbol = addsymbol(ty, cd->scope, m->name);
                m->fn_symbol->flags |= SYM_MEMBER;
                m->fn_symbol->member = M_ID(name);
        }

        AddClassFields(ty, class, cd->scope, &cd->fields,   class_add_field,   0);
        AddClassFields(ty, class, cd->scope, &cd->s_fields, class_add_s_field, SYM_STATIC);

        RestoreContext(ty, ctx);
}

static void
DeclareSymbols(Ty *ty, Stmt *stmt)
{
        Scope *scope = GetNamespace(ty, stmt->ns);
        Expr *expr;

        PushScope(scope);

        switch (stmt->type) {
        case STATEMENT_OPERATOR_DEFINITION:
        case STATEMENT_FUNCTION_DEFINITION:
                symbolize_lvalue(
                        ty,
                        GetNamespace(ty, stmt->ns),
                        stmt->target,
                        HasBody(stmt->value) && (stmt->target->module == NULL),
                        stmt->pub
                );
                stmt->target->symbol->flags &= ~SYM_TRANSIENT;
                stmt->target->symbol->doc = stmt->doc;
                break;

        case STATEMENT_DEFINITION:
                expr = stmt->value;
                switch (expr->type) {
                case EXPRESSION_BOOLEAN:
                case EXPRESSION_INTEGER:
                case EXPRESSION_STRING:
                case EXPRESSION_REAL:
                FullResolve:
                        symbolize_statement(ty, scope, stmt);
                        break;

                case EXPRESSION_IDENTIFIER:
                        if ((expr->symbol = TryResolveIdentifier(ty, expr)) != NULL) {
                                goto FullResolve;
                        }
                        // fall

                default:
                        if (stmt->cnst) {
                                goto FullResolve;
                        }

                        symbolize_decl(ty, scope, stmt->target, stmt->pub);
                }

                if (stmt->target->type == EXPRESSION_IDENTIFIER) {
                        stmt->target->symbol->doc = stmt->doc;
                }
                break;

        case STATEMENT_IF:
                if (!stmt->iff.neg) {
                        break;
                }
                for (int i = 0; i < vN(stmt->iff.parts); ++i) {
                        struct condpart *part = v__(stmt->iff.parts, i);
                        fix_part(ty, part, scope);
                        if (part->target != NULL && part->def) {
                                symbolize_decl(ty, scope, part->target, false);
                        }
                }
                break;
        }

        PopScope();
}

static void
DefinePending(Ty *ty)
{
        for (u32 i = 0; i < vN(STATE.pending); ++i) {
                Stmt *stmt = v__(STATE.pending, i);
                DeclareSymbols(ty, stmt);
        }
        v0(STATE.pending);
}

void
IntroduceDefinitions(Ty *ty, Stmt *stmt)
{
        if (stmt == NULL) {
                return;
        }

        Stmt *last = (vN(STATE.pending) > 0) ? *vvL(STATE.pending) : NULL;

        switch (stmt->type) {
        case STATEMENT_FUNCTION_DEFINITION:
                if (!HasBody(stmt->value)) {
                        avP(STATE.pending, stmt);
                        DefinePending(ty);
                        DT(stmt->value->_type, "FUNC == %s::%s", stmt->target->module, stmt->target->identifier);
                        DT(stmt->target->symbol->type);
                }
                if (
                        (last == NULL)
                     || (last->ns != stmt->ns)
                     || (last->type != STATEMENT_FUNCTION_DEFINITION)
                     || (strcmp(last->value->name, stmt->value->name) != 0)
                ) {
                        DefinePending(ty);
                        avP(STATE.pending, stmt);
                }
                break;

        default:
        Eager:
                avP(STATE.pending, stmt);
                DefinePending(ty);
        }
}

void
define_operator(Ty *ty, Scope *scope, Stmt *s)
{
        if (scope == NULL) {
                scope = GetNamespace(ty, s->ns);
        }

        if (HasBody(s->value)) {
                DeclareSymbols(ty, s);
        }

        RedpillFun(ty, scope, s->value, NULL);

        symbolize_op_def(ty, scope, s);
}

void
define_macro(Ty *ty, Stmt *s, bool fun)
{
        DefinePending(ty);

        symbolize_statement(ty, STATE.global, s);
        s->target->symbol->flags |= fun ? SYM_FUN_MACRO : SYM_MACRO;
        s->target->symbol->flags &= ~SYM_TRANSIENT;
        s->target->symbol->doc = s->doc;
        s->type = STATEMENT_FUNCTION_DEFINITION;

        add_location_info(ty);
        v00(STATE.expression_locations);

        byte_vector code_save = STATE.code;
        v00(STATE.code);

        ProgramAnnotation an = STATE.annotation;
        STATE.annotation = (ProgramAnnotation){0};

        emit_statement(ty, s, false);

        INSN(HALT);

        STATE.annotation = an;

        add_location_info(ty);
        v00(STATE.expression_locations);

        void *ctx = PushContext(ty, s);
        vm_exec(ty, vv(STATE.code));
        RestoreContext(ty, ctx);

        STATE.code = code_save;
}

bool
is_fun_macro(Ty *ty, char const *module, char const *id)
{
        Symbol *s = NULL;

        if (module == NULL) {
                s = scope_lookup(ty, STATE.global, id);
        } else {
                Scope *mod = search_import_scope(module);
                if (mod != NULL) {
                        s = scope_lookup(ty, mod, id);
                }
        }

        return (s != NULL) && SymbolIsFunMacro(s);
}

bool
is_macro(Ty *ty, char const *module, char const *id)
{
        Symbol *s = NULL;

        if (module == NULL) {
                s = scope_lookup(ty, STATE.global, id);
        } else {
                Scope *mod = search_import_scope(module);
                if (mod != NULL) {
                        s = scope_lookup(ty, mod, id);
                }
        }

        return (s != NULL) && SymbolIsMacro(s);
}

bool
compiler_symbolize_expression(Ty *ty, Expr *e, Scope *scope)
{
        EVAL_DEPTH += 1;

        if (TY_CATCH_ERROR()) {
                EVAL_DEPTH -= 1;
                return false;
        }

        if (scope == NULL) {
                symbolize_expression(ty, STATE.global, e);
        } else {
                STATE.fscope = scope->function;
                symbolize_expression(ty, scope, e);
        }

        type_iter(ty);

        EVAL_DEPTH -= 1;
        TY_CATCH_END();

        return true;
}

void
compiler_set_type_of(Ty *ty, Stmt *stmt)
{
        symbolize_lvalue(ty, GetNamespace(ty, stmt->ns), stmt->target, false, false);
        symbolize_expression(ty, GetNamespace(ty, stmt->ns), stmt->value);
        stmt->target->symbol->type = type_fixed(ty, type_resolve(ty, stmt->value));
}

void
compiler_clear_location(Ty *ty)
{
        STATE.start = STATE.end = STATE.mstart = STATE.mend = Nowhere;
}

Value
compiler_render_template(Ty *ty, Expr *e)
{
        Value v;

        if (TY_CATCH_ERROR()) {
                v = Err(ty, vSsz(TyError(ty)));
                vmE(&v);
        }

        if (vN(e->template.stmts) == 1) {
                v = tystmt(ty, v__(e->template.stmts, 0));
                goto End;
        }

        Array *a = vA();

        for (usize i = 0; i < vN(e->template.stmts); ++i) {
                vAp(a, tystmt(ty, v__(e->template.stmts, i)));
        }

        v = tagged(ty, TyMulti, ARRAY(a), NONE);

End:
        for (usize i = 0; i < vN(e->template.holes); ++i) {
                vmX();
        }

        TY_CATCH_END();

        return v;
}

int
CompilationDepth(Ty *ty)
{
        int n = 0;

        for (ContextEntry *ctx = ContextList; ctx != NULL; ctx = ctx->next) {
                n += 1;
        }

        return n;
}

inline static int
ExpressionTypeWidth(Expr const *e)
{
        if (
                (e == NULL)
             && (e->type == EXPRESSION_STATEMENT)
             && (e->type == STATEMENT_EXPRESSION)
        ) {
                return 0;
        }

        return strlen(ExpressionTypeName(e));
}

int
WriteExpressionOrigin(Ty *ty, byte_vector *out, Expr const *e)
{
        char buffer[512];

        if (
                (e == NULL)
             || (e->type == EXPRESSION_STATEMENT)
             || (e->type == STATEMENT_EXPRESSION)
        ) {
                return 0;
        }

        char const *file = GetExpressionModule(e);
        int line = e->start.line;
        int col = e->start.col;

        if (e->type == EXPRESSION_CTX_INFO) {
                return dump(
                        out,
                        "%43s%s\n",
                        "",
                        e->string
                );
        }

        int etw = 0;
        int margin = 44 - etw;

        snprintf(
                buffer,
                sizeof buffer - 1,
                "%*s %s%s%s:%s%d%s:%s%d %s%*s%s",
                margin,
                "expanded from",
                TERM(34),
                file,
                TERM(39),
                TERM(33),
                line + 1,
                TERM(39),
                TERM(33),
                col + 1,
                TERM(95),
                etw + !!etw + !!etw,
                (etw > 0) ? ExpressionTypeName(e) : " | ",
                TERM(39)
        );

        char const *where = buffer;
        int m = strlen(buffer) - 7*strlen(TERM(00));

        while (m > 54) {
                m -= 1;
                where += 1;
        }

        int n = dump(
                out,
                "\n%s       ",
                where
        );

        char const *prefix;
        char const *suffix;
        char const *source;

        prefix = source = e->start.s;
        suffix = e->end.s;

        char const *eol = strchr(prefix, '\n');

        if (eol != NULL && suffix > eol)
                suffix = eol;

        while (prefix[-1] != '\0' && prefix[-1] != '\n')
                --prefix;

        while (isspace(prefix[0]))
                ++prefix;

        int before = source - prefix;
        int length = suffix - source;
        int after = strcspn(suffix, "\n");

        n += dump(
                out,
                "%s%.*s%s%s%.*s%s%s%.*s",
                "",
                before,
                prefix,
                "",
                TERM(34),
                length,
                source,
                TERM(39),
                TERM(22),
                after,
                suffix
        );

        n += dump(
                out,
                "\n%*s%s%s",
                before + 61,
                "",
                "",
                TERM(34)
        );

        for (int i = 0; i < length; ++i)
                xvP(*out, '^');

        n += dump(
                out,
                "%s%s",
                TERM(39),
                TERM(22)
        );

        return n;
}

Value
TyTraceEntryFor(Ty *ty, Expr const *e)
{
        Value trace;
        Value func = NIL;
        Value class = NIL;

        GC_STOP();
        if (e->xfunc != NULL) {
                if (e->xfunc->name != NULL) {
                        func = vSsz(e->xfunc->name);
                }
                if (e->xfunc->class != -1) {
                        class = vSsz(class_name(ty, e->xfunc->class));
                }
        }
        trace = vTn(
                "file", (e->mod == NULL || e->mod->path == NULL) ? NIL : xSz(e->mod->path),
                "module", vSsz(GetExpressionModule(e)),
                "start", vTn(
                        "line", INTEGER(e->start.line + 1),
                        "col", INTEGER(e->start.col + 1)
                ),
                "end", vTn(
                        "line", INTEGER(e->end.line + 1),
                        "col", INTEGER(e->end.col + 1)
                ),
                "fn", func,
                "class", class
        );
        GC_RESUME();

        return trace;
}

Value
CompilationTraceArray(Ty *ty)
{
        Array *trace = vA();

        GC_STOP();

        for (ContextEntry *ctx = ContextList; ctx != NULL; ctx = ctx->next) {
                if (
                        (ctx->e == NULL)
                     || (ctx->e->type == EXPRESSION_STATEMENT)
                     || (ctx->e->type == STATEMENT_EXPRESSION)
                ) {
                        continue;
                }
                vAp(trace, TyTraceEntryFor(ty, ctx->e));
        }

        GC_RESUME();

        return ARRAY(trace);
}

void
CompilationTrace(Ty *ty, byte_vector *out)
{
        int etw = 0;
        //for (ContextEntry *ctx = ContextList; ctx != NULL; ctx = ctx->next) {
        //        etw = max(etw, ExpressionTypeWidth(ctx->e));
        //}

        for (ContextEntry *ctx = ContextList; ctx != NULL; ctx = ctx->next) {
                while (ctx == ctx->next) {
                        ctx = ctx->next;
                }

                if (WriteExpressionTrace(ty, out, ctx->e, etw, ctx == ContextList) == 0) {
                        continue;
                }

                if (WriteExpressionOrigin(ty, out, ctx->e->origin) == 0) {
                        continue;
                }
        }
}

int
WriteExpressionTrace(Ty *ty, byte_vector *out, Expr const *e, int etw, bool first)
{
        char buffer[1024], fun_buffer[256];

        if (e == NULL) {
                return 0;
        }

        if (e->type == STATEMENT_EXPRESSION) {
                return WriteExpressionTrace(
                        ty,
                        out,
                        ((Stmt const *)e)->expression,
                        etw,
                        first
                );
        }

        if (e->type == EXPRESSION_STATEMENT) {
                return WriteExpressionTrace(
                        ty,
                        out,
                        (Expr const *)e->statement,
                        etw,
                        first
                );
        }

        char const *file = GetExpressionModule(e);
        int line = e->start.line;
        int col = e->start.col;

        if (e->type == EXPRESSION_CTX_INFO) {
                return dump(
                        out,
                        "%43s%s\n",
                        "",
                        e->string
                );
        }

        int vt100bytes = 0;

        if (e->xfunc != NULL && e->xfunc->name != NULL) {
                vt100bytes += strlen(TERM(36;1));
                vt100bytes += strlen(TERM(0));
                if (e->xfunc->class == -1) {
                        snprintf(
                                fun_buffer,
                                sizeof fun_buffer,
                                "[%s%s%s]",
                                TERM(36;1),
                                e->xfunc->name,
                                TERM(0)
                        );
                } else {
                        vt100bytes += strlen(TERM(94));
                        vt100bytes += strlen(TERM(0));
                        snprintf(
                                fun_buffer,
                                sizeof fun_buffer,
                                "[%s%s%s.%s%s%s]",
                                TERM(94),
                                class_name(ty, e->xfunc->class),
                                TERM(0),
                                TERM(36;1),
                                e->xfunc->name,
                                TERM(0)
                        );
                }
        } else {
                fun_buffer[0] = '\0';
        }

        etw = min(etw, 24);
        int margin = 44 - etw;

        vt100bytes += 7 * strlen(TERM(00));
        snprintf(
                buffer,
                sizeof buffer,
                "%*s %s%s%s%s:%s%d%s:%s%d %s%*s%s",
                margin,
                first ? "at" : "from",
                TERM(34),
                file,
                TERM(39),
                fun_buffer,
                TERM(33),
                line + 1,
                TERM(39),
                TERM(33),
                col + 1,
                TERM(95),
                etw + !!etw + !!etw,
                (etw > 0) ? ExpressionTypeName(e) : " | ",
                TERM(39)
        );

        char const *where = buffer;
        int m = strlen(buffer) - vt100bytes;

        while (m > 54) {
                m -= 1;
                where += 1;
        }

        int n = dump(
                out,
                "\n%s near: ",
                where
        );

        char const *prefix;
        char const *suffix;
        char const *source;

        prefix = source = e->start.s;
        suffix = e->end.s;

        char const *eol = strchr(prefix, '\n');

        if (eol != NULL && suffix > eol)
                suffix = eol;

        while (prefix[-1] != '\0' && prefix[-1] != '\n')
                --prefix;

        while (isspace(prefix[0]))
                ++prefix;

        int before = source - prefix;
        int length = suffix - source;
        int after = strcspn(suffix, "\n");

        n += dump(
                out,
                "%s%.*s%s%s%.*s%s%s%.*s",
                TERM(32),
                before,
                prefix,
                first ? TERM(1) : "",
                first ? TERM(91) : TERM(31),
                length,
                source,
                TERM(32),
                TERM(22),
                after,
                suffix
        );

        n += dump(
                out,
                "\n%*s%s%s",
                before + 61,
                "",
                first ? TERM(1) : "",
                first ? TERM(91) : TERM(31)
        );

        for (int i = 0; i < length; ++i)
                xvP(*out, '^');

        n += dump(
                out,
                "%s%s",
                TERM(39),
                TERM(22)
        );

        return n;
}

void
WriteExpressionSourceHeading(Ty *ty, byte_vector *out, int cols, Expr const *e)
{
        int path_len = term_width(e->mod->path, -1);
        int pad = max(0, (cols - path_len - 4));
        int pad_l = (pad / 4);
        int pad_r = pad - pad_l;

        dump(out, "%s", TERM(38:2:96:96:96));

        for (int i = 0; i < pad_l; ++i) {
                dump(out, "━");
        }

        dump(out, "┫ %s%s%s ┣", TERM(93;1), e->mod->path, TERM(38:2:96:96:96));

        for (int i = 0; i < pad_r; ++i) {
                dump(out, "━");
        }

        dump(out, "%s\n", TERM(0));
}

void
WriteExpressionSourceContext(Ty *ty, byte_vector *out, Expr const *e)
{
        char const *start = e->start.s;
        char const *end   = e->end.s;

        int line0 = e->start.line;
        int line1 = e->end.line;

        // Seek back a few lines for context
        for (int i = 0; i < 6; ++i) {
                if (start[-1] == '\n') {
                        --start;
                        --line0;
                }
                while (start[-1] != '\0' && start[-1] != '\n') {
                        --start;
                }
        }

        // And ahead a few lines
        for (int i = 0; i < 4; ++i) {
                while (end[0] != '\0' && end[0] != '\n') {
                        ++end;
                }
                if (end[0] == '\n') {
                        ++end;
                        ++line1;
                }
        }

        for (int line = line0; start < end; ++line) {
                char const *line_start = start;
                char const *line_end = strchr(line_start, '\n');
                if (line_end == NULL || line_end > end) {
                        line_end = end;
                }

                if (line == e->start.line && line == e->end.line) {
                        int before = e->start.s - line_start;
                        int length = e->end.s - e->start.s;
                        int after = line_end - e->end.s;
                        dump(
                                out,
                                "%s%4d%s | %.*s%s%.*s%s%.*s%s\n",
                                TERM(91),
                                line + 1,
                                TERM(0),
                                before,
                                line_start,
                                TERM(1;91;4:3),
                                length,
                                e->start.s,
                                TERM(0),
                                after,
                                e->end.s,
                                TERM(0)
                        );
                } else {
                        dump(
                                out,
                                "%s%4d%s | %s%.*s%s\n",
                                (line >= e->start.line && line <= e->end.line) ? TERM(91) : "",
                                line + 1,
                                TERM(0),
                                (line >= e->start.line && line <= e->end.line) ? TERM(91) : "",
                                (int)(line_end - line_start),
                                line_start,
                                TERM(0)
                        );
                }

                start = line_end;
                if (start[0] == '\n') {
                        ++start;
                }
        }
}

char const *
NextCaption(ProgramAnnotation *annotation, char const *pc)
{
        while (
                annotation->i < vN(annotation->map) &&
                pc > v__(annotation->map, annotation->i)
        ) {
                annotation->i += 1;
        }

        if (
                annotation->i == vN(annotation->map) ||
                pc != v__(annotation->map, annotation->i)
        ) {
                return NULL;
        }

        return v__(annotation->captions, annotation->i++);
}

char const *
DumpProgram(
        Ty *ty,
        byte_vector *out,
        char const *name,
        char const *code,
        char const *end,
        bool incl_sub_fns
)
{
#define CASE(i) case INSTR_ ## i:
#define PRINTVALUE(x)                                                                      \
        _Generic(                                                                          \
            (x),                                                                           \
            int:         dump(out, " %s%d%s", TERM(32), (x), TERM(0)),                     \
            intmax_t:    dump(out, " %s%"PRIiMAX"%s", TERM(32), (x), TERM(0)),             \
            double:      dump(out, " %s%f%s", TERM(32), (x), TERM(0)),                     \
            float:       dump(out, " %s%f%s", TERM(32), (x), TERM(0)),                     \
            bool:        dump(out, " %s%s%s", TERM(32), (x) ? "true" : "false", TERM(0)),  \
            uptr:        dump(out, " %"PRIuPTR, (x))                                       \
        )

        byte_vector after = {0};

#define DUMPSTR(s)    (!DebugScan && (xvP(*out, ' '), dumpstr(out, (s)), 0))
#define SKIPSTR()     (DUMPSTR(c), (c += strlen(c) + 1))
#define READSTR(s)    (((s) = c), SKIPSTR())
#define READVALUE(x)  (memcpy(&x, c, sizeof x), (c += sizeof x), (!DebugScan && ((PRINTVALUE(x)), 0)))
#define READVALUE_(x) (memcpy(&x, c, sizeof x), (c += sizeof x))
#define READMEMBER(n) (READVALUE_((n)), DUMPSTR(n == -1 ? "<$>" : M_NAME((n))))
#define READCLASS(n) (READVALUE_((n)), DUMPSTR(n == -1 ? "<$>" : class_name(ty, (n))))

        uptr pc = (uptr)code;
        ProgramAnnotation *annotation = NULL;

        for (int i = 0; i < vN(annotations); ++i) {
                if (
                        pc >= v__(annotations, i).start
                     && pc <  v__(annotations, i).end
                ) {
                        annotation = &v__(annotations, i);
                        annotation->i = 0;
                        break;
                }
        }

        if (code == NULL) {
                for (int i = 0; i < vN(annotations); ++i) {
                        STATE.annotation = v__(annotations, i);
                        DumpProgram(
                                ty,
                                out,
                                v__(annotations, i).name,
                                (char const *)v__(annotations, i).start,
                                (char const *)v__(annotations, i).end,
                                incl_sub_fns
                        );
                }
                return end;
        }

        uptr s;
        intmax_t k;
        bool b = false;
        double x;
        int n, nkw = 0, i, j, tag;

        bool DebugScan = DEBUGGING;
        u32 limit = UINT32_MAX;
        uptr DebugHistory[8] = {0};

        dump(
                out,
                "%s%s: %s%s: %s%s:%s\n",
                TERM(32),
                name,
                TERM(34),
                (annotation == NULL) ? "" : annotation->module,
                TERM(33),
                (annotation == NULL) ? "" : annotation->name,
                TERM(0)
        );
        //dump(out, "%s%s:%s\n", TERM(34), name, TERM(0));
        dont_printf("        %s%s:%s\n", TERM(34), name, TERM(0));

        char const *caption = NULL;

        for (char const *c = code; end == NULL || c < end; DebugScan || xvP(*out, '\n')) {
                uptr pc = (uptr)c;

                if (DEBUGGING) {
                        if (--limit == 0) break;
                        memmove(
                                DebugHistory,
                                DebugHistory + 1,
                                (sizeof DebugHistory) - sizeof DebugHistory[0]
                        );
                        DebugHistory[countof(DebugHistory) - 1] = pc;
                }

                ptrdiff_t begin = out->count;

                if (!DebugScan && annotation != NULL) while (
                        (caption = NextCaption(annotation, c)) != NULL &&
                        caption[0] == ':'
                ) {
                        dump(out, "            %s%s:%s\n", TERM(95), caption + 1, TERM(0));
                        dont_printf("            %s%s:%s\n", TERM(95), caption + 1, TERM(0));
                }

#ifdef TY_PROFILER
                extern istat prof;
                extern FILE *ProfileOut;

                void
                color_sequence(float p, char *out);

                char color_buffer[64] = {0};
                istat_entry *stat = istat_lookup(&prof, c);

                i64 max_ticks, total_ticks;
                istat_count(&prof, &max_ticks, &total_ticks);

                if (*PTERM(0)) {
                        color_sequence(stat == NULL ? 0.0 : 0.75 * stat->t / (double)max_ticks, color_buffer);
                }

                bool exact = (stat == NULL) || stat->n < 1000000;

                dump(
                        out,
                        "%s%7td%s            %s%5.2f%% %6d%s  %8dK %s%s%s",
                        TERM(94), pc, TERM(0),
                        color_buffer,
                        (stat == NULL) ? 0 : 100.0 * stat->t / (double)total_ticks,
                        (stat == NULL) ? 0 : exact ? stat->n : stat->n / 1000,
                        exact ? " " : "K",
                        (stat == NULL) ? 0 : stat->t / 1000,
                        TERM(93), GetInstructionName(*c), TERM(0)
                );
#else
                if (DebugScan && c == ty->ip) {
                        for (int i = 0; i < countof(DebugHistory); ++i) {
                                if (DebugHistory[i] != 0) {
                                        c = (char const *)DebugHistory[i];
                                        break;
                                }
                        }
                        dont_printf("Hit IP:\n");
                        for (int i = 0; i < countof(DebugHistory); ++i) {
                                dont_printf("   [%d] = %ju\n", i, DebugHistory[i]);
                        }
                        DebugScan = false;
                        limit = 2 * countof(DebugHistory);
                        continue;
                }

                if (DEBUGGING && c == ty->ip) {
                        dump(
                                out,
                                "                    %s%7td%s       %s-->  %s%s%s",
                                TERM(92), pc, TERM(0),
                                TERM(92),
                                TERM(93;4), GetInstructionName(*c), TERM(0)
                        );
                } else if (!DebugScan) {
                        dump(
                                out,
                                "                    %s%7td%s            %s%s%s",
                                TERM(94), pc, TERM(0),
                                TERM(93), GetInstructionName(*c), TERM(0)
                        );
                }
#endif

                dont_printf(
                        "%s%7td%s            %s%s%s      %ju\n",
                        TERM(94), pc, TERM(0),
                        TERM(93), GetInstructionName(*c), TERM(0),
                        (uptr)ty->ip
                );

                switch ((unsigned char)*c++) {
                CASE(NOP)
                        break;
                CASE(LOAD_GLOBAL)
                CASE(LOAD_THREAD_LOCAL)
                CASE(LOAD_LOCAL)
                CASE(LOAD_CAPTURED)
                CASE(LOAD_REF)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        SKIPSTR();
#endif
                        break;
                CASE(CHECK_INIT)
                        break;
                CASE(CAPTURE)
                        READVALUE(i);
                        READVALUE(j);
                        break;
                CASE(DECORATE)
                        READVALUE(s);
                        break;
                CASE(EXEC_CODE)
                        READVALUE(s);
                        break;
                CASE(DUP)
                CASE(DUP2)
                        break;
                CASE(JUMP)
                        READVALUE(n);
                        break;
                CASE(JUMP_IF)
                        READVALUE(n);
                        break;
                CASE(JUMP_IF_NOT)
                        READVALUE(n);
                        break;
                CASE(JUMP_IF_NONE)
                        READVALUE(n);
                        break;
                CASE(JUMP_IF_NIL)
                        READVALUE(n);
                        break;
                CASE(JUMP_IF_TYPE)
                CASE(JNI)
                CASE(JII)
                        READVALUE(n);
                        READVALUE(i);
                        break;
                CASE(JLT)
                CASE(JLE)
                CASE(JGT)
                CASE(JGE)
                CASE(JEQ)
                CASE(JNE)
                CASE(JUMP_OR)
                CASE(JUMP_AND)
                CASE(JUMP_WTF)
                        READVALUE(n);
                        break;
                CASE(TARGET_GLOBAL)
                CASE(ASSIGN_GLOBAL)
                        READVALUE(n);
                        break;
                CASE(TARGET_LOCAL)
                CASE(ASSIGN_LOCAL)
                        READVALUE(n);
                        break;
                CASE(TARGET_REF)
                        READVALUE(n);
                        break;
                CASE(TARGET_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        // TODO
                        SKIPSTR();
#endif
                        break;
                CASE(TARGET_MEMBER)
                CASE(TARGET_SELF_MEMBER)
                        READMEMBER(n);
                        break;
                CASE(TARGET_SUBSCRIPT)
                        break;
                CASE(ASSIGN)
                        break;
                CASE(MAYBE_ASSIGN)
                        break;
                CASE(TAG_PUSH)
                        READVALUE(tag);
                        break;
                CASE(ARRAY_REST)
                        READVALUE(n);
                        READVALUE(i);
                        READVALUE(j);
                        break;
                CASE(TUPLE_REST)
                        READVALUE(n);
                        READVALUE(i);
                        break;
                CASE(RECORD_REST)
                        READVALUE(n);
                        c = ALIGNED_FOR(int, c);
                        while (*(int const *)c != -1) c += sizeof (int);
                        c += sizeof (int);
                        break;
                CASE(THROW_IF_NIL)
                        break;
                CASE(UNTAG_OR_DIE)
                        READVALUE(tag);
                        break;
                CASE(STEAL_TAG)
                        break;
                CASE(TRY_STEAL_TAG)
                        READVALUE(n);
                        break;
                CASE(BAD_MATCH)
                        break;
                CASE(BAD_DISPATCH);
                        break;
                CASE(BAD_CALL)
                        SKIPSTR();
                        SKIPSTR();
                        break;
                CASE(BAD_ASSIGN)
                        SKIPSTR();
                        break;
                CASE(THROW)
                CASE(RETHROW)
                        break;
                CASE(FINALLY)
                        break;
                CASE(END_TRY)
                        break;
                CASE(CATCH)
                        break;
                CASE(TRY)
                {
                        READVALUE(n);
                        READVALUE(n);
                        READVALUE(n);
                        READVALUE(b);
                        break;
                }
                CASE(DROP)
                CASE(ENTER)
                        break;
                CASE(PUSH_DROP_GROUP)
                        break;
                CASE(PUSH_DROP)
                        break;
                CASE(PUSH_DEFER_GROUP)
                        break;
                CASE(DEFER)
                        break;
                CASE(CLEANUP)
                        break;
                CASE(ENSURE_LEN)
                        READVALUE(n);
                        READVALUE(n);
                        break;
                CASE(ENSURE_LEN_TUPLE)
                        READVALUE(n);
                        READVALUE(n);
                        break;
                CASE(ENSURE_EQUALS_VAR)
                        READVALUE(n);
                        break;
                CASE(TRY_ASSIGN_NON_NIL)
                        READVALUE(n);
                        break;
                CASE(TRY_REGEX)
                        READVALUE(n);
                        READVALUE_(s);
                        dump(out, " %s/%s/%s", TERM(92), ((Regex *)s)->pattern, TERM(38));
                        break;
                CASE(ASSIGN_REGEX_MATCHES)
                        READVALUE(n);
                        break;
                CASE(ENSURE_DICT)
                        READVALUE(n);
                        break;
                CASE(ENSURE_CONTAINS)
                        READVALUE(n);
                        break;
                CASE(ENSURE_SAME_KEYS)
                        READVALUE(n);
                        break;
                CASE(TRY_INDEX)
                        READVALUE(n);
                        READVALUE(i);
                        READVALUE(b);
                        break;
                CASE(TRY_INDEX_TUPLE)
                        READVALUE(n);
                        READVALUE(i);
                        break;
                CASE(TRY_TUPLE_MEMBER)
                        READVALUE(n);
                        READVALUE(b);
                        READMEMBER(n);
                        break;
                CASE(TRY_TAG_POP)
                        READVALUE(n);
                        READVALUE(tag);
                        break;
                CASE(POP)
                        break;
                CASE(UNPOP)
                        break;
                CASE(INTEGER)
                        READVALUE(k);
                        break;
                CASE(REAL)
                        READVALUE(x);
                        break;
                CASE(BOOLEAN)
                        READVALUE(b);
                        break;
                CASE(STRING)
                        SKIPSTR();
                        break;
                CASE(CLASS)
                        READVALUE(tag);
                        break;
                CASE(TAG)
                        READVALUE(tag);
                        break;
                CASE(REGEX)
                        READVALUE(s);
                        break;
                CASE(ARRAY)
                CASE(ARRAY0)
                        break;
                CASE(TUPLE)
                        READVALUE(n);
                        while (n --> 0) {
                                READVALUE_(i);
                                if (!DebugScan) switch (i) {
                                case -1: dump(out, " %s_%s", TERM(96),   TERM(0)); break;
                                case -2: dump(out, " %s*%s", TERM(95;1), TERM(0)); break;
                                default: DUMPSTR(M_NAME(i));
                                }
                        }
                        break;
                CASE(GATHER_TUPLE)
                        break;
                CASE(DICT)
                        break;
                CASE(DICT_DEFAULT)
                        break;
                CASE(SELF)
                        break;
                CASE(NIL)
                        break;
                CASE(FMT1)
                CASE(FMT2)
                        break;
                CASE(TO_STRING)
                        break;
                CASE(YIELD)
                CASE(YIELD_SOME)
                CASE(YIELD_NONE)
                        break;
                CASE(MAKE_GENERATOR)
                        break;
                CASE(VALUE)
                        READVALUE_(s);
                        if (!DebugScan) {
                                dump(out, " %s", VSC((Value *)s));
                        }
                        dont_printf(" %s", VSC((Value *)s));
                        break;
                CASE(TYPE)
                        READVALUE_(s);
                        if (!DebugScan) {
                                dump(out, " %s", type_show(ty, (Type *)s));
                        }
                        dont_printf(" %s", type_show(ty, (Type *)s));
                        break;
                CASE(EVAL)
                CASE(EXPRESSION)
                        READVALUE(s);
                        break;
                CASE(RENDER_TEMPLATE)
                        READVALUE_(s);
                        if (!DebugScan) xvP(*out, ' ');
                        if (!DebugScan) dump_source_of((Expr *)s, out);
                        break;
                CASE(TRAP)
                CASE(TRAP_TY)
                        break;
                CASE(DEBUG)
                        SKIPSTR();
                        break;
                CASE(GET_NEXT)
                        break;
                CASE(LOOP_ITER)
                        break;
                CASE(LOOP_CHECK);
                        READVALUE(n);
                        READVALUE(n);
                        break;
                CASE(SPREAD_CHECK);
                        READVALUE(n);
                        READVALUE(b);
                        break;
                CASE(ARRAY_COMPR)
                        break;
                CASE(DICT_COMPR)
                        READVALUE(n);
                        break;
                CASE(PUSH_INDEX)
                        READVALUE(n);
                        break;
                CASE(READ_INDEX)
                        break;
                CASE(SENTINEL)
                        break;
                CASE(NONE)
                        break;
                CASE(NONE_IF_NIL)
                        break;
                CASE(CLEAR_RC)
                        break;
                CASE(GET_EXTRA)
                        break;
                CASE(FIX_EXTRA)
                        break;
                CASE(FIX_TO)
                        READVALUE(n);
                        break;
                CASE(SWAP)
                        break;
                CASE(REVERSE)
                        READVALUE(n);
                        break;
                CASE(MULTI_ASSIGN)
                        READVALUE(n);
                        break;
                CASE(MAYBE_MULTI)
                        READVALUE(n);
                        break;
                CASE(JUMP_IF_SENTINEL)
                        READVALUE(n);
                        break;
                CASE(CLEAR_EXTRA)
                        break;
                CASE(PUSH_NTH)
                        READVALUE(n);
                        break;
                CASE(PUSH_ARRAY_ELEM)
                        READVALUE(n);
                        READVALUE(b);
                        break;
                CASE(PUSH_TUPLE_ELEM)
                        READVALUE(n);
                        break;
                CASE(PUSH_TUPLE_MEMBER)
                        READVALUE(b);
                        READMEMBER(n);
                        break;
                CASE(PUSH_ALL)
                        break;
                CASE(CONCAT_STRINGS)
                        READVALUE(n);
                        break;
                CASE(RANGE)
                CASE(INCRANGE)
                        break;
                CASE(TRY_MEMBER_ACCESS)
                CASE(MEMBER_ACCESS)
                        READMEMBER(n);
                        break;
                CASE(SELF_MEMBER_ACCESS)
                        READMEMBER(n);
                        break;
                CASE(TRY_GET_MEMBER)
                CASE(GET_MEMBER)
                        break;
                CASE(SLICE)
                CASE(SUBSCRIPT)
                CASE(NOT)
                CASE(QUESTION)
                CASE(NEG)
                CASE(COUNT)
                CASE(ADD)
                CASE(SUB)
                CASE(MUL)
                CASE(DIV)
                CASE(MOD)
                CASE(EQ)
                CASE(NEQ)
                CASE(CHECK_MATCH)
                CASE(LT)
                CASE(GT)
                CASE(LEQ)
                CASE(GEQ)
                CASE(CMP)
                CASE(GET_TAG)
                CASE(LEN)
                CASE(INC)
                CASE(DEC)
                CASE(PRE_INC)
                CASE(POST_INC)
                CASE(PRE_DEC)
                CASE(POST_DEC)
                CASE(MUT_ADD)
                CASE(MUT_MUL)
                CASE(MUT_DIV)
                CASE(MUT_MOD)
                CASE(MUT_SUB)
                CASE(MUT_AND)
                CASE(MUT_OR)
                CASE(MUT_XOR)
                CASE(MUT_SHL)
                CASE(MUT_SHR)
                        break;
                CASE(BINARY_OP)
                        READVALUE_(n);
                        DUMPSTR(intern_entry(&xD.b_ops, n)->name);
                        break;
                CASE(UNARY_OP)
                        READVALUE_(n);
                        DUMPSTR(intern_entry(&xD.members, n)->name);
                        break;
                CASE(DEFINE_TAG)
                {
                        int tag, super, t, n;
                        READVALUE(tag);
                        READVALUE(super);
                        READVALUE(n);
                        READVALUE(t);
                        while (n --> 0) {
                                SKIPSTR();
                        }
                        while (t --> 0) {
                                SKIPSTR();
                        }
                        break;
                }
                CASE(DEFINE_CLASS)
                {
                        i32 class;
                        i32   m,   g,   s;
                        i32 s_m, s_g, s_s;

                        READVALUE(class);

                        READVALUE(s_m);
                        READVALUE(s_g);
                        READVALUE(m);
                        READVALUE(g);
                        READVALUE(s);

                        while (s_m --> 0) { READMEMBER(i); }
                        while (s_g --> 0) { READMEMBER(i); }
                        while (  m --> 0) { READMEMBER(i); }
                        while (  g --> 0) { READMEMBER(i); }
                        while (  s --> 0) { READMEMBER(i); }
                        break;
                }
                CASE(INIT_STATIC_FIELD)
                        READCLASS(i);
                        READMEMBER(i);
                        break;
                CASE(FUNCTION)
                {
                        Value v = {0};

                        c = ALIGNED_FOR(int, c);

                        // n: bound_caps
                        READVALUE_(n);

                        v.info = (int *) c;

                        int hs = v.info[0];
                        int size  = v.info[1];
                        int nEnv = v.info[2];
                        int bound = v.info[3];

                        int ncaps = (n > 0) ? nEnv - n : nEnv;

                        LOG("Header size: %d", hs);
                        LOG("Code size: %d", size);
                        LOG("Bound: %d", bound);
                        LOG("ncaps: %d", ncaps);

                        if (
                                !incl_sub_fns
                             || (DEBUGGING && (ty->ip > c + hs + size))
                        ) {
                                c += hs + size;
                        } else {
                                char signature[256];

                                snprintf(
                                        signature,
                                        sizeof signature,
                                        "%s%s",
                                        name_of(&v),
                                        (proto_of(&v) == NULL) ? "()" : proto_of(&v)
                                );

                                dump(out, " %s%s%s", TERM(96), signature, TERM(0));
                                c = DumpProgram(
                                        ty,
                                        &after,
                                        signature,
                                        c + hs,
                                        c + hs + size,
                                        incl_sub_fns
                                );
                        }

                        for (int i = 0; i < ncaps; ++i) {
                                READVALUE_(b);
                                READVALUE_(j);
                        }

                        break;
                }
                CASE(BIND_INSTANCE)
                CASE(BIND_GETTER)
                CASE(BIND_SETTER)
                CASE(BIND_STATIC)
                        READVALUE(n);
                        READVALUE(n);
                        break;
                CASE(NAMESPACE)
                        READVALUE(s);
                        break;
                CASE(PATCH_ENV)
                        READVALUE(n);
                        break;
                CASE(OPERATOR)
                        READVALUE(i);
                        READVALUE(j);
                        break;
                CASE(TAIL_CALL)
                        break;
                CASE(CALL)
                        READVALUE(n);
                        READVALUE(nkw);
                        for (int i = 0; i < nkw; ++i) {
                                SKIPSTR();
                        }
                        break;
                CASE(TRY_CALL_METHOD)
                CASE(CALL_METHOD)
                CASE(CALL_SELF_METHOD)
                        READVALUE(n);
                        READMEMBER(n);
                        READVALUE(nkw);
                        for (int i = 0; i < nkw; ++i) {
                                SKIPSTR();
                        }
                        break;
                CASE(SAVE_STACK_POS)
                        break;
                CASE(POP_STACK_POS)
                CASE(POP_STACK_POS_POP)
                        break;
                CASE(MULTI_RETURN)
                        READVALUE(n);
                        break;
                CASE(RETURN_IF_NOT_NONE)
                CASE(RETURN)
                CASE(RETURN_PRESERVE_CTX)
                        break;
                CASE(HALT)
                        if (end == NULL) goto End;
                }

                if (!DebugScan && caption != NULL) {
                        int width = term_width(
                                v_(*out, begin),
                                out->count - begin
                        );

                        while (width < 70) {
                                xvP(*out, ' ');
                                width += 1;
                        }

                        dump(out, "  %s#  %s%s", TERM(34;1), caption, TERM(0));
                }
        }
End:
        if (!DEBUGGING && vN(after) > 0) {
                xvP(*out, '\n');
                xvPn(*out, vv(after), vN(after));
                xvF(after);
        }

        xvP(*out, '\n');

        return end;
}

bool
IsTopLevel(Symbol const *sym)
{
        Scope *s = sym->scope;

        while (s->namespace)
                s = s->parent;

        return (GlobalScope == s)
            || (GlobalScope == s->parent);
}

CompileState
PushCompilerState(Ty *ty, char const *file, u32 flags)
{
        CompileState old = STATE;

        Module *tmp_mod = amA0(sizeof (Module));
        tmp_mod->name = file;
        tmp_mod->path = file;
        tmp_mod->source = NULL;
        tmp_mod->scope = scope_new(ty, file, GlobalScope, true);

        STATE = freshstate(ty, tmp_mod);
        STATE._parse = (flags & TYC_PARSE);
        STATE._eval  = (flags & TYC_EVAL);

        for (isize i = 0; i < vN(modules); ++i){
                avP(
                        STATE.imports,
                        ((struct import) {
                                .mod = v__(modules, i),
                                .name = v__(modules, i)->name,
                                .pub = true
                        })
                );
        }

        return old;
}

void
PopCompilerState(Ty *ty, CompileState saved)
{
        STATE = saved;
}

CompileState *
TyCompilerState(Ty *ty)
{
        return &STATE;
}

void
CompilerScopePush(Ty *ty)
{
        STATE.pscope = scope_new(ty, "(block)", STATE.pscope, false);
}

void
CompilerScopePop(Ty *ty)
{
        STATE.pscope = STATE.pscope->parent;
}

void
CompilerBlackpill(Ty *ty, Stmt *s)
{
        InjectRedpill(ty, s);
}

bool
CompilerResolveExpr(Ty *ty, Expr *e)
{
        Scope *s0 = STATE.active;
        Scope *s1 = (STATE.func != NULL)
                  ? STATE.func->scope
                  : NULL;
        Scope *s2 = (STATE.class != NULL)
                  ? STATE.class->def->class.scope
                  : NULL;

        Scope *scope;
        if (s0 != NULL && s1 != NULL) {
                scope = scope_is_subscope(s0, s1) ? s0 : s1;
        } else if (s0 != NULL && s2 != NULL) {
                scope = scope_is_subscope(s0, s2) ? s0 : s2;
        } else {
                scope = (s0 != NULL) ? s0
                      : (s1 != NULL) ? s1
                      : STATE.global;
        }

        if (TY_CATCH_ERROR()) {
                return false;
        }

        symbolize_expression(ty, scope, e);

        TY_CATCH_END();

        return true;
}

bool
CompilerGetModuleTokens(Ty *ty, TokenVector *out, char const *name)
{
        Module *mod = GetModule(ty, name);
        if (mod == NULL) {
                return false;
        }

        *out = mod->tokens;

        return true;
}

char const *
CompilerGetModuleSource(Ty *ty, char const *name)
{
        Module *mod = GetModule(ty, name);
        if (mod == NULL) {
                return NULL;
        }

        return mod->source;
}

Module *
CompilerCurrentModule(Ty *ty)
{
        return STATE.module;
}

Module *
CompilerGetModule(Ty *ty, char const *name)
{
        return GetModule(ty, name);
}

bool
CompilerReloadModule(
        Ty *ty,
        Module *mod,
        char const *source
)
{
        Module saved = *mod;
        i64 symbol  = scope_get_symbol(ty);

        ScopeReset(mod->scope);
        v00(mod->imports);
        v00(mod->tokens);
        mod->prog = NULL;
        mod->source = NULL;
        mod->flags |= MOD_RELOADING;
        mod->scope->reloading = true;

        if (TY_CATCH_ERROR()) {
                mod->flags &= ~MOD_RELOADING;
                mod->scope->reloading = false;
                scope_set_symbol(ty, symbol);
                *mod = saved;
                return false;
        }

        STATE = freshstate(ty, mod);

        if (source == NULL) {
                source = slurp_module(ty, mod->name, NULL);
        }

        Stmt **prog = compile(ty, source);

        TY_CATCH_END();

        PatchModule(ty, mod, prog);
        v00(STATE.code);

        mod->scope->reloading = false;
        mod->flags &= ~MOD_RELOADING;

        return true;
}

Symbol *
CompilerFindDefinition(Ty *ty, Module *mod, i32 line, i32 col)
{
        Module *save = STATE.module;
        STATE.module = mod;

        QueryResult = NULL;
        QueryExpr = NULL;
        QueryLine = line;
        QueryCol = col;
        QueryFile = mod->path;

        Stmt **prog = mod->prog;
        for (int i = 0; (prog[i] != NULL) && (QueryResult == NULL); ++i) {
                on_god(ty, prog[i]);
        }

        STATE.module = save;

        return (Symbol *)QueryResult;
}

void
CompilerResetState(Ty *ty)
{
        v0(STATE.imports);
}

inline static Value
SymbolToCompletionItem(Ty *ty, Symbol const *sym, i32 depth)
{
        return vTn(
                "name",  xSz(sym->identifier),
                "doc",   (sym->doc == NULL) ? NIL : xSz(sym->doc),
                "type",  xSz(type_show(ty, sym->type)),
                "kind",  INTEGER(6),
                "depth", INTEGER(depth)
        );
}

static void
AddScopeCompletions(
        Ty *ty,
        Scope *scope,
        char const *pre,
        ValueVector *completions,
        i32 max
)
{
        static symbol_vector symbols;
        static i32Vector depths;

        if (scope == NULL) {
                return;
        }

        v0(symbols);
        v0(depths);

        ScopeCompletions(
                ty,
                scope,
                pre,
                &symbols,
                &depths,
                max,
                !scope->external
        );

        for (u32 i = 0; i < vN(symbols); ++i) {
                xvP(
                        *completions,
                        SymbolToCompletionItem(
                                ty,
                                v__(symbols, i),
                                v__(depths, i)
                        )
                );
        }
}

bool
CompilerSuggestCompletions(
        Ty *ty,
        Module *mod,
        i32 line,
        i32 col,
        ValueVector *completions
)
{
        Module *save = STATE.module;
        STATE.module = mod;

        QueryResult = NULL;
        QueryExpr = NULL;
        QueryLine = line;
        QueryCol = col;
        QueryFile = mod->path;

        Stmt **prog = mod->prog;
        for (int i = 0; prog != NULL && prog[i] != NULL; ++i) {
                on_god(ty, prog[i]);
        }

        STATE.module = save;

        if (QueryExpr == NULL) {
                return false;
        }

        Scope *scope = NULL;

        switch (QueryExpr->type) {
        case EXPRESSION_IDENTIFIER:
                XXLOG(
                        "OBJECT IS AN IDENTIFIER: %s::%s (namespace=%s)",
                        QueryExpr->module ? QueryExpr->module : "<>",
                        QueryExpr->identifier,
                        QueryExpr->namespace ? edbg(QueryExpr->namespace) : "<>"
                );
                scope = (QueryExpr->module != NULL) && (*QueryExpr->module != '\0')
                                                       ? search_import_scope(QueryExpr->module)
                      : (QueryExpr->namespace != NULL) ? QueryExpr->namespace->scope
                      : (QueryExpr->xscope    != NULL) ? QueryExpr->xscope
                      : STATE.global;

                XXLOG("QueryExpr=IDENTIFIER: scope=%s", scope ? scope_name(ty, scope) : "<null>");
                if (scope != NULL) {
                        AddScopeCompletions(
                                ty,
                                scope,
                                QueryExpr->identifier,
                                completions,
                                16
                        );
                }
                break;

        case EXPRESSION_MEMBER_ACCESS:
                if (QueryExpr->object->type == EXPRESSION_MODULE) {
                        XXLOG("OBJECT IS A MODULE: %s", QueryExpr->object->name);
                        AddScopeCompletions(
                                ty,
                                QueryExpr->object->scope,
                                QueryExpr->member->identifier,
                                completions,
                                16
                        );
                } else {
                        XXLOG("OBJECT IS NOT A MODULE: %s", QueryExpr->object->name);
                        type_completions(
                                ty,
                                QueryExpr->object->_type,
                                QueryExpr->member->identifier,
                                completions
                        );
                }
                break;
        }

        return true;
}

/* vim: set sw=8 sts=8 expandtab: */
