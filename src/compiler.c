#include <stdio.h>
#include <stdalign.h>
#include <ctype.h>
#include <string.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdnoreturn.h>

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
#include "test.h"
#include "lex.h"
#include "parse.h"
#include "tags.h"
#include "class.h"
#include "vm.h"
#include "compiler.h"
#include "istat.h"

#define PLACEHOLDER_JUMP(t, name) JumpPlaceholder name = (PLACEHOLDER_JUMP)(ty, (t))
#define LABEL(name) JumpLabel name = (LABEL)(ty)


#define PATCH_OFFSET(i)                                           \
        do {                                                      \
                int dist = state.code.count - i - sizeof dist;    \
                memcpy(state.code.items + i, &dist, sizeof dist); \
        } while (0)

#define PATCH_JUMP(name)                            \
        do {                                        \
                PATCH_OFFSET((name).off);           \
                annotate(":L%d", (name).label + 1); \
        } while (0)

#define JUMP(loc)                                                          \
        do {                                                               \
                annotate("%sL%d%s", TERM(95), (loc).label + 1, TERM(0));   \
                emit_instr(ty, INSTR_JUMP);                                \
                emit_int(ty, (loc).off - state.code.count - sizeof (int)); \
        } while (0)

#define JUMP_IF_NOT(loc)                                                   \
        do {                                                               \
                annotate("%sL%d%s", TERM(95), (loc).label + 1, TERM(0));   \
                emit_instr(ty, INSTR_JUMP_IF_NOT);                         \
                emit_int(ty, (loc).off - state.code.count - sizeof (int)); \
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
                EMIT_GROUP_LABEL(state.match_fails, "Fail"); \
                emit_instr(ty, INSTR_ ## instr);             \
                avP(state.match_fails, state.code.count);    \
                emit_int(ty, 0);                             \
        } while (0)

#define SAVE_JB                        \
        jmp_buf jb_;                   \
        memcpy(&jb_, &jb, sizeof jb)

#define RESTORE_JB memcpy(&jb, &jb_, sizeof jb)

#define CHECK_INIT() if (CheckConstraints) { emit_instr(ty, INSTR_CHECK_INIT); }

#ifdef TY_ENABLE_PROFILING
#define KEEP_LOCATION(e) true
#else
#define KEEP_LOCATION(e) ((e)->type > EXPRESSION_KEEP_LOC)
#endif

#if 0
  #define INSTR_SAVE_STACK_POS INSTR_SAVE_STACK_POS), emit_int(ty, __LINE__
  #define INSTR_RESTORE_STACK_POS INSTR_RESTORE_STACK_POS), emit_int(ty, __LINE__
#endif

bool CheckConstraints = true;
bool ProduceAnnotation = true;
size_t GlobalCount = 0;

static jmp_buf *ujb;
static jmp_buf jb;
static char const *Error;

static int builtin_modules;
static int BuiltinCount;

static vec(struct module) modules;
static vec(ProgramAnnotation) annotations;
static CompileState state;
static vec(location_vector) location_lists;
static vec(void *) source_map;
static Scope *global;
static uint64_t t;
static char const EmptyString[] = "\0";
static char const UnknownString[] = "\0(unknown location)";
static Location Nowhere = { 0, 0, EmptyString + 1 };
static Location UnknownStart = { 0, 0, UnknownString + 1 };
static Location UnknownEnd = { 0, 0, UnknownString + sizeof UnknownString - 1 };

typedef struct context_entry ContextEntry;

struct context_entry {
        ContextEntry *next;
        char const *info;
        Expr *e;
};

static ContextEntry *ContextList;

static void
symbolize_statement(Ty *ty, Scope *scope, Stmt *s);

static void
symbolize_pattern(Ty *ty, Scope *scope, Expr *e, Scope *reuse, bool def);

static void
symbolize_expression(Ty *ty, Scope *scope, Expr *e);

static bool
emit_statement(Ty *ty, Stmt const *s, bool want_result);

static void
emit_expression(Ty *ty, Expr const *e);

static void
emit_expr(Ty *ty, Expr const *e, bool need_loc);

static void
emit_assignment(Ty *ty, Expr *target, Expr const *e, bool maybe, bool def);

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
invoke_macro(Ty *ty, Expr *e, Scope *scope);

static void
invoke_fun_macro(Ty *ty, Scope *, Expr *e);

static void
emit_spread(Ty *ty, Expr const *e, bool nils);

static void
compile(Ty *ty, char const *source);

char const *
DumpProgram(Ty *ty, byte_vector *out, char const *name, char const *code, char const *end);

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
                        state.annotation.map,                                \
                        (void const *)(uintptr_t)state.code.count            \
                );                                                           \
                xvP(                                                         \
                        state.annotation.captions,                           \
                        (void const *)(uintptr_t)state.annotation.text.count \
                );                                                           \
                dump(&state.annotation.text, __VA_ARGS__);                   \
                xvP(state.annotation.text, '\0');                            \
        } while (0)

static void
PatchAnnotation(ProgramAnnotation *annotation, void const *base)
{
        for (int i = 0; i < annotation->map.count; ++i) {
                annotation->map.items[i] = (void const *)(
                                (uintptr_t)annotation->map.items[i]
                              + (uintptr_t)base
                );
        }

        for (int i = 0; i < annotation->captions.count; ++i) {
                annotation->captions.items[i] = (void const *)(
                                (uintptr_t)annotation->captions.items[i]
                              + (uintptr_t)annotation->text.items
                );
        }

        annotation->start += (uintptr_t)base;
        annotation->end += (uintptr_t)base;

        annotation->patched = true;
}

inline static Expr *
NewExpr(Ty *ty, int t)
{
        Expr *e = amA0(sizeof *e);
        e->arena = GetArenaAlloc(ty);
        e->start = UnknownStart;
        e->end = UnknownEnd;
        e->filename = state.filename;
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
        s->filename = state.filename;
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

inline static Value
unwrap(Ty *ty, Value const *wrapped)
{
        Value v = *wrapped;

        if (v.tags != 0) {
                v.tags = tags_pop(ty, v.tags);
        }

        if (v.tags == 0) {
                v.type &= ~VALUE_TAGGED;
        }

        return v;
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
                vec_nogc_push(*b, '.');
        }

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                for (char const *m = e->module; m && *m; ++m) {
                        vec_nogc_push(*b, *m == '/' ? '.' : *m);
                }
                vec_nogc_push_n(*b, e->identifier, strlen(e->identifier));
                break;
        case EXPRESSION_MEMBER_ACCESS:
                vec_nogc_push_n(*b, e->member_name, strlen(e->member_name));
                break;
        case EXPRESSION_MODULE:
        case EXPRESSION_NAMESPACE:
                vec_nogc_push_n(*b, e->name, strlen(e->name));
                break;
        }

        return true;
}

static char const *
QualifiedName(Expr const *e)
{
        _Thread_local static byte_vector name = {0};

        name.count = 0;

        if (QualifiedName_(e, &name)) {
                vec_nogc_push(name, '\0');
                return name.items;
        } else {
                return "(error)";
        }
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
        } else if (e->type > EXPRESSION_MAX_TYPE) {
                return StatementTypeNames[e->type - (STATEMENT_TYPE_START + 1)];
        } else {
                return ExpressionTypeNames[e->type];
        }
}

void
colorize_code(
        char const *expr_color,
        char const *base_color,
        Location const *start,
        Location const *end,
        char *out,
        size_t n
)
{
        char const *prefix = start->s;
        char const *eol = start->s + strcspn(start->s, "\n");
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
        if (ContextList != NULL && ContextList->e == ctx)
                return ContextList;

        ContextEntry *new = amA(sizeof *new);
        new->next = ContextList;
        new->info = NULL;
        new->e = (void *)ctx;

        SWAP(ContextEntry *, new, ContextList);

        //printf("PushContext(ty, %s) -> %p: depth=%d\n", ExpressionTypeName(ctx), ContextList, CompilationDepth(ty));

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

inline static void
RestoreContext(Ty *ty, void *ctx)
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

noreturn static void
fail(Ty *ty, char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        int sz = ERR_SIZE;
        int n = snprintf(ERR, sz, "%s%sCompileError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        if (n < sz) n += vsnprintf(ERR + n, sz - n, fmt, ap);
        va_end(ap);

        if (n < sz) n += snprintf(ERR + n, sz - n, "\n%s", CompilationTrace(ty));

        Error = ERR;

        if (ujb != NULL) {
                longjmp(*ujb, 1);
        } else {
                longjmp(jb, 1);
        }
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

inline static void
DebugExpr(Ty *ty, Expr const *e)
{
        Value v = tyexpr(ty, e);
        XLOG("%s", VSC(&v));
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
        return sclone_malloc(buffer);
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

inline static void
emit_instr(Ty *ty, int c)
{
        avP(state.code, (char)c);
}

static int
method_cmp(void const *a_, void const *b_)
{
        Expr const *a = *(Expr const **)a_;
        Expr const *b = *(Expr const **)b_;

        int o = (a->name == NULL || b->name == NULL) ? 0 : strcmp(a->name, b->name);

        return (o != 0) ? o : (a->t - b->t);
}

static char *
try_slurp_module(Ty *ty, char const *name)
{
        char pathbuf[512];

        char const *home = getenv("HOME");

        if (home == NULL)
                home = getenv("USERPROFILE");

        if (home == NULL)
                fail(ty, "unable to get USERPROFILE / HOME from the environment");

        snprintf(pathbuf, sizeof pathbuf, "%s/.ty/%s.ty", home, name);

        char *source = slurp(ty, pathbuf);
        if (source == NULL) {
                snprintf(pathbuf, sizeof pathbuf, "%s.ty", name);
                source = slurp(ty, pathbuf);
        }

        return source;
}

static char *
slurp_module(Ty *ty, char const *name)
{
        char *source = try_slurp_module(ty, name);

        if (source == NULL) {
                fail(ty, "failed to load module: %s", name);
        }

        return source;
}

static void
add_location(Ty *ty, Expr const *e, size_t start_off, size_t end_off)
{
        if (e->start.line == -1 && e->start.col == -1)
                return;

        //printf("Location: (%zu, %zu) (%d) '%.*s'\n", start_off, end_off, e->type, (int)(e->end.s - e->start.s), e->start.s);

        avP(
                state.expression_locations,
                ((struct eloc) {
                        .start_off = start_off,
                        .end_off = end_off,
                        .start = e->start,
                        .end = e->end,
                        .filename = state.filename,
                        .e = e
                })
        );
}

static void
add_location_info(Ty *ty)
{
        struct eloc *locs = state.expression_locations.items;
        for (int i = 0; i < state.expression_locations.count; ++i) {
                //printf("start_off=%ju\n", locs[i].start_off);
                locs[i].p_start = (uintptr_t)(state.code.items + locs[i].start_off);
                locs[i].p_end = (uintptr_t)(state.code.items + locs[i].end_off);
        }

        qsort(
                state.expression_locations.items,
                state.expression_locations.count,
                sizeof (struct eloc),
                eloc_cmp
        );

        xvP(location_lists, state.expression_locations);
}

inline static void
begin_finally(Ty *ty)
{
        vvL(state.tries)->finally = true;
}

inline static void
end_finally(Ty *ty)
{
        vvL(state.tries)->finally = false;
}

inline static bool
inside_finally(Ty *ty)
{
        return state.tries.count != 0 && vvL(state.tries)->finally;
}

inline static TryState *
get_try(Ty *ty, int i)
{
        if (i < state.tries.count) {
                return vvL(state.tries) - i;
        } else {
                return NULL;
        }
}

inline static void
begin_try(Ty *ty)
{
        TryState try = {
                .t = ++t,
                .finally = false
        };

        avP(state.tries, try);
}

inline static void
end_try(Ty *ty)
{
        vvX(state.tries);
}

inline static LoopState *
get_loop(Ty *ty, int i)
{
        if (i < state.loops.count) {
                return vvL(state.loops) - i;
        } else {
                return NULL;
        }
}

inline static void
begin_loop(Ty *ty, bool wr, bool each)
{
        LoopState loop = {
                .t = ++t,
                .resources = state.resources,
                .wr = wr,
                .each = each
        };

        avP(state.loops, loop);
}

inline static void
end_loop(Ty *ty)
{
        vvX(state.loops);
}

inline static bool
is_call(Expr const *e)
{
        return e->type == EXPRESSION_METHOD_CALL || e->type == EXPRESSION_FUNCTION_CALL;
}

inline static bool
is_tag(Ty *ty, Expr const *e)
{
        assert(e->type == EXPRESSION_IDENTIFIER);

        Scope const *scope = (e->module == NULL || *e->module == '\0') ? state.global : get_import_scope(ty, e->module);
        Symbol *sym = scope_lookup(ty, scope, e->identifier);

        return sym != NULL && sym->tag != -1;
}

inline static bool
is_const(Ty *ty, Scope const *scope, char const *name)
{
        Symbol const *s = scope_lookup(ty, scope, name);

        return s != NULL && s->cnst;
}

static bool
any_variadic(Expr * const *args, Expr * const *conds, int n)
{

        for (int i = 0; i < n; ++i) {
                if (
                        args[i] != NULL &&
                        (args[i]->type == EXPRESSION_SPREAD || conds[i] != NULL)
                ) {
                        return true;
                }
        }

        return false;
}

static bool
is_variadic(Expr const *e)
{
        if (e->type == EXPRESSION_FUNCTION_CALL) {
                return any_variadic(
                        e->args.items,
                        e->fconds.items,
                        e->args.count
                );
        } else if (e->type == EXPRESSION_METHOD_CALL) {
                return any_variadic(
                        e->method_args.items,
                        e->mconds.items,
                        e->method_args.count
                );
        }

        return false;
}

inline static Symbol *
addsymbol(Ty *ty, Scope *scope, char const *name)
{
        assert(name != NULL);

        LOG("Declaring %s in scope %s", name, scope_name(ty, scope));

        if (scope_locally_defined(ty, scope, name) && is_const(ty, scope, name) &&
            (scope == state.global || scope == global) && strcmp(name, "_") != 0) {
                fail(
                        ty,
                        "redeclaration of variable %s%s%s%s%s",
                        TERM(1),
                        TERM(34),
                        name,
                        TERM(22),
                        TERM(39)
                );
        }

        Symbol *s = scope_add(ty, scope, name);
        s->file = state.filename;
        s->loc = state.start;

        if (isupper(name[0])) {
                s->public = true;
        }

        LOG("adding symbol: %s -> %d", name, s->symbol);

        return s;
}

inline static Symbol *
getsymbol(Ty *ty, Scope const *scope, char const *name, bool *local)
{
        if (strcmp(name, "_") == 0) {
                fail(
                        ty,
                        "the special identifier %s'_'%s can only be used as an lvalue",
                        TERM(38),
                        TERM(39)
                );
        }

        // Allow -> it + 1 instead of -> _1 + 1
        if (strcmp(name, "it") == 0 && state.implicit_fscope != NULL) {
                name = "_1";
        }

        /*
         * let f = -> function () { let _2 = 4; return _1 + _2; };
         *
         * // f = const . (+ 4)
         */
        if (name[0] == '_' && isdigit(name[1]) && name[2] == '\0' && state.implicit_fscope != NULL) {
                int n = name[1] - '0';
                for (int i = state.implicit_func->params.count + 1; i <= n; ++i) {
                        char b[] = { '_', i + '0', '\0' };
                        char *id = sclonea(ty, b);
                        Symbol *sym = addsymbol(ty, state.implicit_fscope, id);
                        avP(state.implicit_func->params, id);
                        avP(state.implicit_func->param_symbols, sym);
                        avP(state.implicit_func->dflts, NULL);
                        avP(state.implicit_func->constraints, NULL);
                }
        }

        Symbol *s = scope_lookup(ty, scope, name);
        if (s == NULL || s->namespace) {
                fail(
                        ty,
                        "reference to undefined variable: %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        name,
                        TERM(0)
                );
        }

        if (s->scope->external && !s->public)
                fail(ty, "reference to non-public external variable '%s'", name);

        bool is_local = s->scope->function == scope->function;

        if (local != NULL)
                *local = is_local;

        return s;
}

inline static Symbol *
tmpsymbol(Ty *ty, Scope *scope)
{
        static int i;
        static char idbuf[16];

        assert(i <= 9999999);

        sprintf(idbuf, "#%d", i++);

        return scope_add(ty, scope, sclonea(ty, idbuf));
}

static CompileState
freshstate(Ty *ty)
{
        CompileState s = {0};

        s.global = scope_new(ty, "(global)", global, false);
        s.class = -1;
        s.start = s.end = s.mstart = s.mend = Nowhere;

        return s;
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

inline static void
resolve_class_choices(Ty *ty, Scope *scope, Expr *e, int_vector *cs)
{
        if (e->type == EXPRESSION_IDENTIFIER && e->symbol->class != -1) {
                avP(*cs, e->symbol->class);
        } else if (e->type == EXPRESSION_BIT_OR) {
                resolve_class_choices(ty, scope, e->left, cs);
                resolve_class_choices(ty, scope, e->right, cs);
        } else {
                fail(ty, "bad operator signature");
        }
}

inline static int
op_signature(Ty *ty, Scope *scope, Expr *e, int_vector *t1, int_vector *t2)
{
        if (e->constraints.count > 0 && e->constraints.items[0] != NULL) {
                symbolize_expression(ty, scope, e->constraints.items[0]);
                resolve_class_choices(ty, scope, e->constraints.items[0], t1);
        } else {
                avP(*t1, CLASS_TOP);
        }

        if (e->constraints.count > 1 && e->constraints.items[1] != NULL) {
                symbolize_expression(ty, scope, e->constraints.items[1]);
                resolve_class_choices(ty, scope, e->constraints.items[1], t2);
        } else {
                avP(*t2, CLASS_TOP);
        }

        if (
                e->params.count == 0 ||
                e->params.count > 2  ||
                e->ikwargs != -1     ||
                e->rest != -1
        ) {
                fail(ty, "bad operator signature");
        }

        return e->params.count;
}

static void
symbolize_op_def(Ty *ty, Scope *scope, Stmt *def)
{
        int_vector t1 = {0};
        int_vector t2 = {0};

        Expr *target = def->target;
        Expr *func = def->value;

        int arity = op_signature(ty, scope, func, &t1, &t2);

        InternSet *set = (arity == 1) ? &xD.u_ops : &xD.b_ops;
        InternEntry *e = intern(set, target->identifier);

        target->symbol = scope_add(ty, global, target->identifier);

        for (int i = 0; i < t1.count; ++i) {
                for (int j = 0; j < t2.count; ++j) {
                        dont_printf(
                                "  %4s :: (%3d) %8s x %-8s (%3d) :: %d\n",
                                e->name,
                                t1.items[i],
                                class_name(ty, t1.items[i]),
                                class_name(ty, t2.items[j]),
                                t2.items[j],
                                target->symbol->i
                        );
                        op_add(e->id, t1.items[i], t2.items[j], target->symbol->i);
                }
        }

        /*
         * We can strip away the constraints now. The checks will only ever be
         * reached when the operands are already known to satisfy them.
         */
        for (int i = 0; i < func->constraints.count; ++i) {
                func->constraints.items[i] = NULL;
        }

        symbolize_expression(ty, scope, func);
}

inline static Expr *
resolve_access(Ty *ty, Scope const *scope, char **parts, int n, Expr *e, bool strict)
{
        static vec(char) mod;
        mod.count = 0;

        Symbol *sym = NULL;

        if (n == 1) {
                sym = scope_lookup(ty, scope, parts[0]);
                if (sym != NULL && !sym->namespace) {
                        return e;
                }
        }

        for (int i = 0; i < n; ++i) {
                if (i > 0) {
                        vec_nogc_push(mod, '/');
                }
                int len = strlen(parts[i]);
                vec_nogc_push_n(mod, parts[i], len);
        }

        vec_nogc_push(mod, '\0');

        Scope *mod_scope = search_import_scope(mod.items);
        if (mod_scope != NULL) {
                e->type = EXPRESSION_MODULE;
                e->name = (n == 1) ? parts[0] : sclonea(ty, mod.items);
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

#ifdef TY_DEBUG_NAMES
        static int d;
        printf("%*sbefore: left=%s, e=%s, part=%s\n", d*4, "", ExpressionTypeName(left), ExpressionTypeName(e), parts[n - 1]);
        d += 1;
        resolve_access(ty, scope, parts, n - 1, left, strict);
        d -= 1;
        printf("%*safter:  left=%s, e=%s, part=%s\n", d*4, "", ExpressionTypeName(left), ExpressionTypeName(e), id);
#else
        resolve_access(ty, scope, parts, n - 1, left, strict);
#endif

        if (left->type == EXPRESSION_IDENTIFIER || left->type == EXPRESSION_MEMBER_ACCESS)
                return e;

        sym = scope_lookup(ty, left->scope, id);
        if (sym == NULL) {
                if (!strict) return NULL;
                //DebugExpr(ty, e);
                state.end = e->end;
                fail(
                        ty,
                        "reference to undefined variable: %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        id,
                        TERM(0)
                );
        } else if (
                !sym->public &&
                (
                        left->scope->external ||
                        !scope_is_subscope(ty, left->scope, state.global)
                )
        ) {
                if (!strict) return NULL;
                state.end = e->end;
                fail(
                        ty,
                        "reference to non-public external symbol %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        id,
                        TERM(0)
                );
        }

        if (sym->namespace) {
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

                vec_init(fc.fkwconds);
                for (size_t i = 0; i < fc.kws.count; ++i) {
                        avP(fc.fkwconds, NULL);
                }

                Expr *f = fc.function = NewExpr(ty, EXPRESSION_IDENTIFIER);
                f->start = left->start;
                f->end = e->end;
                f->filename = state.filename;
                f->identifier = id;
                f->namespace = left;
                f->module = NULL;
                f->symbol = sym;
                f->symbolized = true;

                *e = fc;
        } else {
                ZERO_EXPR(e);
                e->type = EXPRESSION_IDENTIFIER;
                e->identifier = id;
                e->namespace = left;
                e->module = NULL;
                e->symbol = sym;
                e->symbolized = true;
        }

        return e;
}

void
fixup_access(Ty *ty, Scope const *scope, Expr *e, bool strict)
{
        StringVector parts = {0};

        char const *name;
        Location start = e->start;
        Location end = e->end;

        if (scope == NULL) {
                scope = state.global;
        }

        if (e->type == EXPRESSION_MEMBER_ACCESS) {
                name = e->member_name;
                start = e->start;
                end = e->end;
        } else if (e->type == EXPRESSION_METHOD_CALL) {
                name = e->method_name;
                start = e->object->start;
                end = e->object->end;
                while (*end.s != '\0' && *end.s != '(') {
                        end.s += 1;
                }
        } else {
                return;
        }

        Expr const *o = e->object;

        for (;;) {
                if (o->type == EXPRESSION_MEMBER_ACCESS) {
                        o = o->object;
                } else if (o->type == EXPRESSION_NAMESPACE && o->parent != NULL) {
                        o = o->parent;
                } else {
                        break;
                }
        }

        if (
                (o->type != EXPRESSION_MODULE) &&
                (o->type != EXPRESSION_NAMESPACE || o->parent != NULL) &&
                (o->type != EXPRESSION_IDENTIFIER || o->module != NULL)
        ) {
                return;
        }

        if (o->type == EXPRESSION_IDENTIFIER) {
                Symbol *sym = scope_lookup(ty, scope, o->identifier);
                if (sym != NULL && !sym->namespace) {
                        return;
                }
        }

        avP(parts, (char *)name);

        o = e->object;

       for (;;) {
                if (o->type == EXPRESSION_MEMBER_ACCESS) {
                        avI(parts, o->member_name, 0);
                        o = o->object;
                } else if (o->type == EXPRESSION_NAMESPACE && o->parent != NULL) {
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

#ifdef TY_DEBUG_NAMES
        printf("parts: ");
        for (int i = 0; i < parts.count; ++i) {
                if (i > 0) putchar('.');
                printf("%s", parts.items[i]);
        }
        putchar('\n');
#endif

        resolve_access(ty, scope, parts.items, parts.count, (Expr *)e, strict);

#ifdef TY_DEBUG_NAMES
        printf("resolved to: %s\n", ExpressionTypeName(e));
#endif
}

static Scope *
search_import_scope(char const *name)
{
        for (int i = 0; i < state.imports.count; ++i)
                if (strcmp(name, state.imports.items[i].name) == 0)
                        return state.imports.items[i].scope;

        return NULL;
}

static Scope *
get_import_scope(Ty *ty, char const *name)
{
        Scope *scope = search_import_scope(name);

        if (scope == NULL) {
                fail(
                        ty,
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

                        if (!ms[i]->function->symbol->fun_macro) {
                                fail(ty, "non-FLM used as method decorator macro");
                        }

                        invoke_fun_macro(ty, scope, ms[i]);

                        if (ms[i]->type != EXPRESSION_FUNCTION) {
                                fail(ty, "method decorator macro returned %s", ExpressionTypeName(ms[i]));
                        }
                }
        }
}

static void
symbolize_methods(Ty *ty, Scope *scope, Expr **ms, int n)
{
        for (int i = 0; i < n; ++i) {
                ms[i]->is_method = true;
                symbolize_expression(ty, scope, ms[i]);
        }
}

static Expr *
mkmulti(Ty *ty, char *name, bool setters)
{
        Expr *multi = NewExpr(ty, EXPRESSION_MULTI_FUNCTION);

        multi->name = name;
        multi->rest = setters ? -1 : 0;
        multi->ikwargs = -1;

        avP(multi->params, "@");
        avP(multi->constraints, NULL);
        avP(multi->dflts, NULL);

        return multi;
}

static void
aggregate_overloads(Ty *ty, expression_vector *ms, bool setters)
{
        int n = ms->count;

        qsort(ms->items, n, sizeof *ms->items, method_cmp);

        for (int i = 0; i + 1 < n; ++i) {
                if (strcmp(ms->items[i]->name, ms->items[i + 1]->name) != 0) {
                        continue;
                }

                char buffer[1024];
                Expr *multi = mkmulti(ty, ms->items[i]->name, setters);

                int m = 0;
                do {
                        ms->items[i + m]->is_overload = true;
                        snprintf(buffer, sizeof buffer, "%s#%d", ms->items[i + m]->name, m + 1);
                        ms->items[i + m]->name = sclonea(ty, buffer);
                        avP(multi->functions, ms->items[i + m]);
                        m += 1;
                } while (i + m < n && strcmp(ms->items[i + m]->name, multi->name) == 0);

                avP(*ms, multi);
        }
}

static void
add_captures(Ty *ty, Expr *pattern, Scope *scope)
{
        /*
         * /(\w+) = (\d+)/ => _0, _1, _2
         */
        struct regex const *re = pattern->regex;

        int n;
        pcre_fullinfo(re->pcre, re->extra, PCRE_INFO_CAPTURECOUNT, &n);

        int n_named;
        pcre_fullinfo(re->pcre, re->extra, PCRE_INFO_NAMECOUNT, &n_named);

        char const *names;
        pcre_fullinfo(re->pcre, re->extra, PCRE_INFO_NAMETABLE, &names);

        pattern->match_symbol = addsymbol(ty, scope, "$0");

        for (int i = 1; i <= n; ++i) {
                char const *nt = names;
                for (int j = 0; j < n_named; ++j) {
                        int capture_index = (nt[0] << 8) + nt[1];
                        nt += 2;

                        if (capture_index == i) {
                                /*
                                 * Don't think clone is necessary here...
                                 */
                                addsymbol(ty, scope, nt);
                                goto NextCapture;
                        }
                }

                /*
                 * This is not a named capture group
                 */
                char id[16];
                sprintf(id, "$%d", i);
                addsymbol(ty, scope, sclonea(ty, id));
        NextCapture:
                ;
        }
}

void
try_symbolize_application(Ty *ty, Scope *scope, Expr *e)
{
        if (scope == NULL) {
                scope = state.global;
        }

        bool tag_pattern = e->type == EXPRESSION_TAG_PATTERN_CALL;

        if (
                tag_pattern ||
                (
                        e->type == EXPRESSION_FUNCTION_CALL &&
                        e->function->type == EXPRESSION_IDENTIFIER
                )
        ) {
                if (!tag_pattern) {
                        symbolize_expression(ty, scope, e->function);
                } else {
                        e->type = EXPRESSION_TAG_PATTERN;
                }
                if (tag_pattern || e->function->symbol->tag != -1) {
                        Expr f = *e;
                        char *identifier = e->function->identifier;
                        char *module = e->function->module;
                        Expr *namespace = e->function->namespace;
                        Expr **tagged = e->args.items;
                        int tagc = e->args.count;
                        Symbol *symbol = e->function->symbol;
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
                                for (int i = 0; i < f.kws.count; ++i) {
                                        avP(items->es, f.kwargs.items[i]);
                                        avP(items->tconds, f.fkwconds.items[i]);
                                        avP(items->required, true);
                                        avP(items->names, f.kws.items[i]);
                                }
                                e->tagged = items;
                        }
                }
        } else if (
                (e->type == EXPRESSION_TAG_APPLICATION)
             && (e->identifier != EmptyString)
        ) {
                e->symbol = e->symbolized ? e->symbol : getsymbol(
                        ty,
                        (e->module == NULL || *e->module == '\0') ? scope : get_import_scope(ty, e->module),
                        e->identifier,
                        NULL
                );
        }
}

static void
symbolize_lvalue_(Ty *ty, Scope *scope, Expr *target, bool decl, bool pub)
{
        state.start = target->start;
        state.end = target->end;

        if (target->filename == NULL)
                target->filename = state.filename;

        if (target->symbolized)
                return;

        void *ctx = PushContext(ty, target);

        fixup_access(ty, scope, target, true);
        try_symbolize_application(ty, scope, target);

        if (target->symbolized)
                goto End;

        switch (target->type) {
        case EXPRESSION_RESOURCE_BINDING:
                if (strcmp(target->identifier, "_") == 0) {
                        target->identifier = gensym(ty);
                }
        case EXPRESSION_SPREAD:
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_MATCH_ANY:
                if (target->type == EXPRESSION_SPREAD) {
                        if (target->value->type != EXPRESSION_IDENTIFIER) {
                                fail(ty, "spread expression used in lvalue context");
                        }
                        char *name = target->value->identifier;
                        ZERO_EXPR(target);
                        target->type = EXPRESSION_MATCH_REST;
                        target->identifier = name;
                        if (strcmp(target->identifier, "*") == 0) {
                                target->identifier = "_";
                        }
                } else if (target->type == EXPRESSION_TAG_PATTERN) {
                        symbolize_lvalue_(ty, scope, target->tagged, decl, pub);
                }
                if (decl) {
                        if (target->module != NULL) {
                                scope = get_import_scope(ty, target->module);
                                pub = true;
                        }
                        target->symbol = addsymbol(ty, scope, target->identifier);
                        target->local = true;
                        symbolize_expression(ty, scope, target->constraint);
                        if (pub) {
                                target->symbol->public = true;
                        }
                } else {
                        if (target->constraint != NULL) {
                                fail(
                                        ty,
                                        "illegal constraint on %s%s%s%s%s in assignment statement",
                                        TERM(1),
                                        TERM(34),
                                        target->identifier,
                                        TERM(39),
                                        TERM(22)
                                );
                        }

                        target->symbol = getsymbol(ty, scope, target->identifier, &target->local);

                        if (target->symbol->cnst) {
                        ConstAssignment:
                                fail(
                                        ty,
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
                        state.resources += 1;
                }
                break;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_expression(ty, scope, target->left);
                symbolize_lvalue_(ty, scope, target->right, decl, pub);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_lvalue_(ty, scope, target->tagged, decl, pub);
                if (target->identifier != EmptyString) {
                        target->symbol = (target->symbol != NULL) ? target->symbol : getsymbol(
                                ty,
                                ((target->module == NULL || *target->module == '\0') ? state.global : get_import_scope(ty, target->module)),
                                target->identifier,
                                NULL
                        );
                }
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < target->elements.count; ++i)
                        symbolize_lvalue_(ty, scope, target->elements.items[i], decl, pub);
                target->atmp = tmpsymbol(ty, scope);
                break;
        case EXPRESSION_DICT:
                if (target->dflt != NULL) {
                        PushContext(ty, target->dflt);
                        fail(ty, "unexpected default clause in dict destructuring");
                }
                for (int i = 0; i < target->keys.count; ++i) {
                        symbolize_expression(ty, scope, target->keys.items[i]);
                        symbolize_lvalue_(ty, scope, target->values.items[i], decl, pub);
                }
                target->dtmp = tmpsymbol(ty, scope);
                break;
        case EXPRESSION_SUBSCRIPT:
                symbolize_expression(ty, scope, target->container);
                symbolize_expression(ty, scope, target->subscript);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                symbolize_expression(ty, scope, target->object);
                break;
        case EXPRESSION_TUPLE:
                target->ltmp = tmpsymbol(ty, scope);
        case EXPRESSION_LIST:
                for (int i = 0; i < target->es.count; ++i) {
                        symbolize_lvalue_(ty, scope, target->es.items[i], decl, pub);
                }
                break;
        default:
                fail(ty, "unexpected %s in lvalue context", ExpressionTypeName(target));
        }

        target->symbolized = true;
End:
        RestoreContext(ty, ctx);
}

static void
symbolize_lvalue(Ty *ty, Scope *scope, Expr *target, bool decl, bool pub)
{
        symbolize_lvalue_(ty, scope, target, decl, pub);

        if (state.resources > 0) {
                target->has_resources = true;
                state.resources = 0;
        }
}

static void
symbolize_pattern_(Ty *ty, Scope *scope, Expr *e, Scope *reuse, bool def)
{
        if (e == NULL)
                return;

        if (e->filename == NULL)
                e->filename = state.filename;

        if (e->symbolized)
                return;

        void *ctx = PushContext(ty, e);

        fixup_access(ty, scope, e, true);
        try_symbolize_application(ty, scope, e);

        if (e->symbolized)
                goto End;

        if (e->type == EXPRESSION_IDENTIFIER && is_tag(ty, e))
                goto Tag;

        state.start = e->start;
        state.end = e->end;

        Symbol *existing;

        switch (e->type) {
        case EXPRESSION_RESOURCE_BINDING:
                if (strcmp(e->identifier, "_") == 0) {
                        e->identifier = gensym(ty);
                }
        case EXPRESSION_IDENTIFIER:
                if (strcmp(e->identifier, "_") != 0 && (is_const(ty, scope, e->identifier) || scope_locally_defined(ty, scope, e->identifier) || e->module != NULL)) {
                        e->type = EXPRESSION_MUST_EQUAL;
                        Scope *s = (e->module == NULL || *e->module == '\0') ? scope : get_import_scope(ty, e->module);
                        e->symbol = getsymbol(ty, s, e->identifier, NULL);
                } else {
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_ALIAS_PATTERN:
        case EXPRESSION_MATCH_ANY:
                        if (reuse != NULL && e->module == NULL && (existing = scope_local_lookup(ty, reuse, e->identifier)) != NULL) {
                                e->symbol = existing;
                        } else {
                                e->symbol = def ? addsymbol(ty, scope, e->identifier) : getsymbol(ty, scope, e->identifier, NULL);
                        }
                        symbolize_expression(ty, scope, e->constraint);
                }
                if (e->type == EXPRESSION_RESOURCE_BINDING) {
                        state.resources += 1;
                } else if (e->type == EXPRESSION_TAG_PATTERN) {
                        symbolize_pattern_(ty, scope, e->tagged, reuse, def);
                } else if (e->type == EXPRESSION_ALIAS_PATTERN) {
                        symbolize_pattern_(ty, scope, e->aliased, reuse, def);
                }
                e->local = true;
                break;
        case EXPRESSION_KW_AND:
                symbolize_pattern_(ty, scope, e->left, reuse, def);
                for (int i = 0; i < e->p_cond.count; ++i) {
                        struct condpart *p = e->p_cond.items[i];
                        symbolize_pattern_(ty, scope, p->target, reuse, p->def);
                        symbolize_expression(ty, scope, p->e);
                }
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < e->elements.count; ++i)
                        symbolize_pattern_(ty, scope, e->elements.items[i], reuse, def);
                break;
        case EXPRESSION_DICT:
                for (int i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(ty, scope, e->keys.items[i]);
                        symbolize_pattern_(ty, scope, e->values.items[i], reuse, def);
                }
                break;
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        symbolize_pattern_(ty, scope, e->es.items[i], reuse, def);
                }
                break;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_expression(ty, scope, e->left);
                symbolize_pattern_(ty, scope, e->right, reuse, def);
                break;
        case EXPRESSION_SPREAD:
                if (e->value->type != EXPRESSION_IDENTIFIER) {
                        fail(ty, "spread expression used in pattern context");
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
                break;
        Tag:
                symbolize_expression(ty, scope, e);
                e->type = EXPRESSION_MUST_EQUAL;
                break;
        case EXPRESSION_CHECK_MATCH:
                symbolize_pattern_(ty, scope, e->left, reuse, def);
                symbolize_expression(ty, scope, e->right);
                break;
        case EXPRESSION_REGEX:
                add_captures(ty, e, scope);
                break;
        default:
                symbolize_expression(ty, scope, e);
                break;
        }

        e->symbolized = true;
End:
        RestoreContext(ty, ctx);
}

static void
symbolize_pattern(Ty *ty, Scope *scope, Expr *e, Scope *reuse, bool def)
{
        symbolize_pattern_(ty, scope, e, reuse, def);

        if (state.resources > 0) {
                e->has_resources = true;
                state.resources = 0;
        }
}


static Expr *
expedite_fun(Ty *ty, Expr *e, void *ctx)
{
        if (e->type != EXPRESSION_FUNCTION_CALL)
                return e;

        if (e->function->type != EXPRESSION_IDENTIFIER) {
                return e;
        }

        Symbol *sym = scope_lookup(ty, ctx, e->function->identifier);

        if (sym == NULL) {
                return e;
        }

        symbolize_expression(ty, ctx, e->function);

        if (e->function->symbol->fun_macro) {
                invoke_fun_macro(ty, ctx, e);
        }

        return e;
}

static void
comptime(Ty *ty, Scope *scope, Expr *e)
{
        symbolize_expression(ty, scope, e->operand);
        Value v = tyeval(ty, e->operand);
        Location mstart = state.mstart;
        Location mend = state.mend;
        state.mstart = state.start;
        state.mend = state.end;
        *e = *cexpr(ty, &v);
        symbolize_expression(ty, scope, e);
        state.mstart = mstart;
        state.mend = mend;
}

static void
invoke_fun_macro(Ty *ty, Scope *scope, Expr *e)
{
        add_location_info(ty);
        vec_init(state.expression_locations);

        byte_vector code_save = state.code;
        vec_init(state.code);

        ProgramAnnotation annotation = state.annotation;
        state.annotation = (ProgramAnnotation) {0};

        int t = e->type;
        e->type = EXPRESSION_FUN_MACRO_INVOCATION;

        emit_expression(ty, e->function);
        emit_instr(ty, INSTR_HALT);

        vec_init(state.expression_locations);

        vm_exec(ty, state.code.items);

        state.code = code_save;
        state.annotation = annotation;

        Value m = *vm_get(ty, 0);
        vmX();

        GC_STOP();

        Scope *mscope = state.macro_scope;
        state.macro_scope = scope;

        void *ctx = PushInfo(ty, e, "invoking function-like macro %s", QualifiedName(e->function));

        for (size_t i = 0;  i < e->args.count; ++i) {
                Value v = tyexpr(ty, e->args.items[i]);
                vmP(&v);
        }

        Value v = vmC(&m, e->args.count);

        Location const mstart = state.mstart;
        Location const mend = state.mend;

        state.mstart = e->start;
        state.mend = e->end;

        Expr *origin = state.origin;
        CloneContext(ty);
        state.origin = ContextList->e;
        *e = *cexpr(ty, &v);
        state.origin = origin;

        state.mstart = mstart;
        state.mend = mend;
        state.macro_scope = mscope;

        RestoreContext(ty, ctx);

        GC_RESUME();
}

static bool
try_fun_macro_op(Ty *ty, Scope *scope, Expr *e)
{
        Symbol *sym = scope_lookup(ty, scope, e->op_name);

        if (sym == NULL || !sym->fun_macro) {
                return false;
        }

        Expr *fun = NewExpr(ty, EXPRESSION_IDENTIFIER);
        fun->symbolized = true;
        fun->identifier = (char *)e->op_name;
        fun->scope = sym->scope;
        fun->symbol = sym;

        Expr *left = e->left;
        Expr *right =  e->right;

        e->type = EXPRESSION_FUNCTION_CALL;
        e->function = fun;

        vec_init(e->args);
        vec_init(e->fconds);

        avP(e->args, left);
        avP(e->fconds, NULL);

        avP(e->args, right);
        avP(e->fconds, NULL);

        invoke_fun_macro(ty, scope, e);

        return true;
}

static Scope *
GetNamespace(Ty *ty, Namespace *ns)
{
        if (ns == NULL)
                return state.global;

        Scope *scope = GetNamespace(ty, ns->next);
        Symbol *sym = scope_lookup(ty, scope, ns->id);

        if (sym == NULL) {
                sym = scope_new_namespace(ty, ns->id, scope);
                sym->public = ns->pub;
#ifdef TY_DEBUG_NAMES
                LOG("new ns %s (scope=%s) added to %s\n", ns->id, scope_name(ty, sym->scope), scope_name(ty, scope));
#endif
        } else if (!sym->namespace) {
                return state.global;
        }

        return sym->scope;
}

static void
symbolize_expression(Ty *ty, Scope *scope, Expr *e)
{
        if (e == NULL)
                return;

        if (e->filename == NULL)
                e->filename = state.filename;

        if (e->symbolized)
                return;

        state.start = e->start;
        state.end = e->end;

        Scope *subscope;

        Expr *func = state.func;
        Expr *implicit_func = state.implicit_func;
        Scope *implicit_fscope = state.implicit_fscope;

        void *ctx = PushContext(ty, e);

        fixup_access(ty, scope, e, true);

        if (e->symbolized)
                goto End;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                LOG("symbolizing var: %s%s%s", (e->module == NULL ? "" : e->module), (e->module == NULL ? "" : "::"), e->identifier);
                if (e->module == NULL && strcmp(e->identifier, "__module__") == 0) {
                        e->type = EXPRESSION_STRING;
                        e->string = state.filename;
                        break;
                }
                if (e->module == NULL && strcmp(e->identifier, "__class__") == 0) {
                        if (state.class != -1) {
                                e->type = EXPRESSION_STRING;
                                e->string = class_name(ty, state.class);
                        } else {
                                e->type = EXPRESSION_NIL;
                        }
                        break;
                }
                if (e->module == NULL && strcmp(e->identifier, "__func__") == 0) {
                        if (state.func && state.func->name != NULL) {
                                e->type = EXPRESSION_STRING;
                                e->string = state.func->name;
                        } else {
                                e->type = EXPRESSION_NIL;
                        }
                        break;
                }
                if (e->module == NULL && strcmp(e->identifier, "__line__") == 0) {
                        e->type = EXPRESSION_INTEGER;
                        e->integer = state.start.line + 1;
                        break;
                }
                // This turned out to be cringe
                if (false && state.class != -1 && e->module == NULL) {
                        Symbol *sym = scope_lookup(ty, scope, e->identifier);
                        if (sym == NULL || sym->scope == state.global || sym->scope == global) {
                                if (class_method(ty, state.class, e->identifier)) {
                                        char const *id = e->identifier;
                                        e->type = EXPRESSION_SELF_ACCESS;
                                        e->member_name = id;
                                        e->maybe = false;
                                        e->object = NewExpr(ty, EXPRESSION_IDENTIFIER);
                                        e->object->identifier = "self";
                                        e->object->start = e->start;
                                        e->object->end = e->end;
                                        symbolize_expression(ty, scope, e->object);
                                        break;
                                }
                        }
                }
                e->symbol = getsymbol(
                        ty,
                        ((e->module == NULL || *e->module == '\0') ? scope : get_import_scope(ty, e->module)),
                        e->identifier,
                        &e->local
                );
                LOG("var %s local", e->local ? "is" : "is NOT");
                if (e->constraint != NULL) {
                        fail(
                                ty,
                                "illegal constraint on %s%s%s%s%s in expression context",
                                TERM(1),
                                TERM(34),
                                e->identifier,
                                TERM(39),
                                TERM(22)
                        );
                }
                break;
        case EXPRESSION_COMPILE_TIME:
                comptime(ty, scope, e);
                break;
        case EXPRESSION_SPECIAL_STRING:
                for (int i = 0; i < e->expressions.count; ++i) {
                        symbolize_expression(ty, scope, e->expressions.items[i]);
                        symbolize_expression(ty, scope, *v_(e->fmt_args, i));
                }
                break;
        case EXPRESSION_TAG:
                e->symbol = getsymbol(
                        ty,
                        ((e->module == NULL || *e->module == '\0') ? state.global : get_import_scope(ty, e->module)),
                        e->identifier,
                        NULL
                );
                break;
        case EXPRESSION_TAG_APPLICATION:
                if (e->identifier != EmptyString) {
                        e->symbol = getsymbol(
                                ty,
                                ((e->module == NULL || *e->module) ? state.global : get_import_scope(ty, e->module)),
                                e->identifier,
                                NULL
                        );
                }
                symbolize_expression(ty, scope, e->tagged);
                break;
        case EXPRESSION_MATCH:
                symbolize_expression(ty, scope, e->subject);
                for (int i = 0; i < e->patterns.count; ++i) {
                        if (e->patterns.items[i]->type == EXPRESSION_LIST) {
                                Scope *shared = scope_new(ty, "(match-shared)", scope, false);
                                for (int j = 0; j < e->patterns.items[i]->es.count; ++j) {
                                        subscope = scope_new(ty, "(match-branch)", scope, false);
                                        symbolize_pattern(ty, subscope, e->patterns.items[i]->es.items[j], shared, true);
                                        scope_copy(ty, shared, subscope);
                                }
                                subscope = shared;
                        } else {
                                subscope = scope_new(ty, "(match-branch)", scope, false);
                                symbolize_pattern(ty, subscope, e->patterns.items[i], NULL, true);
                        }
                        symbolize_expression(ty, subscope, e->thens.items[i]);
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
                symbolize_expression(ty, scope, e->left);
                symbolize_expression(ty, scope, e->right);
                break;
        case EXPRESSION_DEFINED:
                e->type = EXPRESSION_BOOLEAN;
                if (e->module != NULL) {
                        Scope *mscope = search_import_scope(e->module);
                        e->boolean = mscope != NULL && scope_lookup(ty, mscope, e->identifier) != NULL;
                } else {
                        e->boolean = scope_lookup(ty, scope, e->identifier) != NULL;
                }
                break;
        case EXPRESSION_IFDEF:
                if (e->module != NULL) {
                        Scope *mscope = search_import_scope(e->module);
                        if (mscope != NULL && scope_lookup(ty, mscope, e->identifier) != NULL) {
                                e->type = EXPRESSION_IDENTIFIER;
                                symbolize_expression(ty, scope, e);
                                e->type = EXPRESSION_IFDEF;
                        } else {
                                e->type = EXPRESSION_NIL;
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
                scope_capture_all(ty, scope, global);
        case EXPRESSION_PREFIX_HASH:
        case EXPRESSION_PREFIX_BANG:
        case EXPRESSION_PREFIX_QUESTION:
        case EXPRESSION_PREFIX_MINUS:
        case EXPRESSION_PREFIX_AT:
        case EXPRESSION_PREFIX_INC:
        case EXPRESSION_PREFIX_DEC:
        case EXPRESSION_POSTFIX_INC:
        case EXPRESSION_POSTFIX_DEC:
                symbolize_expression(ty, scope, e->operand);
                break;
        case EXPRESSION_CONDITIONAL:
                symbolize_expression(ty, scope, e->cond);
                symbolize_expression(ty, scope, e->then);
                symbolize_expression(ty, scope, e->otherwise);
                break;
        case EXPRESSION_STATEMENT:
                symbolize_statement(ty, scope, e->statement);
                break;
        case EXPRESSION_TEMPLATE:
                for (size_t i = 0; i < e->template.exprs.count; ++i) {
                        symbolize_expression(ty, scope, e->template.exprs.items[i]);
                }
                break;
        case EXPRESSION_FUNCTION_CALL:
                symbolize_expression(ty, scope, e->function);
                if (e->function->type == EXPRESSION_IDENTIFIER && e->function->symbol->fun_macro) {
                        invoke_fun_macro(ty, scope, e);
                        symbolize_expression(ty, scope, e);
                        break;
                }
                for (size_t i = 0;  i < e->args.count; ++i)
                        symbolize_expression(ty, scope, e->args.items[i]);
                for (size_t i = 0;  i < e->args.count; ++i)
                        symbolize_expression(ty, scope, e->fconds.items[i]);
                for (size_t i = 0; i < e->kwargs.count; ++i)
                        symbolize_expression(ty, scope, e->kwargs.items[i]);
                break;
        case EXPRESSION_SUBSCRIPT:
                symbolize_expression(ty, scope, e->container);
                symbolize_expression(ty, scope, e->subscript);
                break;
        case EXPRESSION_SLICE:
                symbolize_expression(ty, scope, e->slice.e);
                symbolize_expression(ty, scope, e->slice.i);
                symbolize_expression(ty, scope, e->slice.j);
                symbolize_expression(ty, scope, e->slice.k);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                symbolize_expression(ty, scope, e->object);
                break;
        case EXPRESSION_METHOD_CALL:
                symbolize_expression(ty, scope, e->object);
                for (size_t i = 0;  i < e->method_args.count; ++i)
                        symbolize_expression(ty, scope, e->method_args.items[i]);
                for (size_t i = 0;  i < e->method_args.count; ++i)
                        symbolize_expression(ty, scope, e->mconds.items[i]);
                for (size_t i = 0; i < e->method_kwargs.count; ++i)
                        symbolize_expression(ty, scope, e->method_kwargs.items[i]);
                break;
        case EXPRESSION_EQ:
        case EXPRESSION_MAYBE_EQ:
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MINUS_EQ:
                symbolize_expression(ty, scope, e->value);
                symbolize_lvalue(ty, scope, e->target, false, false);
                break;
        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_FUNCTION:
                for (int i = 0; i < e->decorators.count; ++i) {
                        symbolize_expression(ty, scope, e->decorators.items[i]);
                }

                state.func = e;

                if (e->name != NULL) {
                        scope = scope_new(ty, "(function name)", scope, false);
                        e->function_symbol = e->is_method ? NULL : addsymbol(ty, scope, e->name);
                        LOG("== SYMBOLIZING %s ==", e->name);
                } else {
                        LOG("== SYMBOLIZING %s ==", "(anon)");
                        e->function_symbol = NULL;
                }

                scope = scope_new(ty, e->name == NULL ? "(anon)" : e->name, scope, true);
                LOG("%s got scope %p (global=%p, state.global=%p)", e->name == NULL ? "(anon)" : e->name, scope, global, state.global);

                if (e->type == EXPRESSION_IMPLICIT_FUNCTION) {
                        state.implicit_fscope = scope;
                        state.implicit_func = e;
                        e->type = EXPRESSION_FUNCTION;
                }

                vec_init(e->param_symbols);

                /*
                 * This is trash.
                 */
                if (e->is_method) {
                        Symbol *s = scope_add_i(ty, scope, "self", e->params.count);
                        s->file = state.filename;
                        s->loc = state.start;
                }

                for (size_t i = 0; i < e->params.count; ++i) {
                        symbolize_expression(ty, scope, e->dflts.items[i]);
                        avP(e->param_symbols, addsymbol(ty, scope, e->params.items[i]));
                }

                for (size_t i = 0; i < e->params.count; ++i) {
                        symbolize_expression(ty, scope, e->constraints.items[i]);
                }

                symbolize_expression(ty, scope, e->return_type);

                symbolize_statement(ty, scope, e->body);

                e->scope = scope;
                e->bound_symbols.items = scope->owned.items;
                e->bound_symbols.count = scope->owned.count;

                state.func = func;
                state.implicit_fscope = implicit_fscope;
                state.implicit_func = implicit_func;

                break;
        case EXPRESSION_WITH:
                subscope = scope_new(ty, "(with)", scope, false);
                symbolize_statement(ty, subscope, e->with.block);
                for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                        for (Symbol *sym = subscope->table[i]; sym != NULL; sym = sym->next) {
                                // Make sure it's not a tmpsymbol(ty) symbol
                                if (!isdigit(sym->identifier[0])) {
                                        avP(vvL(e->with.block->statements)[0]->try.finally->drop, sym);
                                }
                        }
                }
                break;
        case EXPRESSION_THROW:
                symbolize_expression(ty, scope, e->throw);
                break;
        case EXPRESSION_YIELD:
                for (int i = 0; i < e->es.count; ++i) {
                    symbolize_expression(ty, scope, e->es.items[i]);
                }
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i) {
                        symbolize_expression(ty, scope, e->elements.items[i]);
                        symbolize_expression(ty, scope, e->aconds.items[i]);
                }
                break;
        case EXPRESSION_ARRAY_COMPR:
                symbolize_expression(ty, scope, e->compr.iter);
                subscope = scope_new(ty, "(array compr)", scope, false);
                symbolize_lvalue(ty, subscope, e->compr.pattern, true, false);
                symbolize_expression(ty, subscope, e->compr.cond);
                for (size_t i = 0; i < e->elements.count; ++i) {
                        symbolize_expression(ty, subscope, e->elements.items[i]);
                        symbolize_expression(ty, subscope, e->aconds.items[i]);
                }
                break;
        case EXPRESSION_DICT:
                symbolize_expression(ty, scope, e->dflt);
                for (size_t i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(ty, scope, e->keys.items[i]);
                        symbolize_expression(ty, scope, e->values.items[i]);
                }
                break;
        case EXPRESSION_DICT_COMPR:
                symbolize_expression(ty, scope, e->dcompr.iter);
                subscope = scope_new(ty, "(dict compr)", scope, false);
                symbolize_lvalue(ty, subscope, e->dcompr.pattern, true, false);
                symbolize_expression(ty, subscope, e->dcompr.cond);
                for (size_t i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(ty, subscope, e->keys.items[i]);
                        symbolize_expression(ty, subscope, e->values.items[i]);
                }
                break;
        case EXPRESSION_LIST:
                for (int i = 0; i < e->es.count; ++i) {
                        symbolize_expression(ty, scope, e->es.items[i]);
                }
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        symbolize_expression(ty, scope, e->es.items[i]);
                        symbolize_expression(ty, scope, e->tconds.items[i]);
                }
                break;
        case EXPRESSION_SPREAD:
        case EXPRESSION_SPLAT:
                symbolize_expression(ty, scope, e->value);
                break;
        case EXPRESSION_MACRO_INVOCATION:
                invoke_macro(ty, e, scope);
                break;
        case EXPRESSION_MATCH_REST:
                fail(ty, "*<identifier> 'match-rest' pattern used outside of pattern context");
        }

        e->symbolized = true;
End:
        RestoreContext(ty, ctx);
}

static void
symbolize_statement(Ty *ty, Scope *scope, Stmt *s)
{
        if (s == NULL)
                return;

        state.start = s->start;
        state.end = s->end;

        Scope *subscope;

        if (scope == state.global && s->ns != NULL)
                scope = GetNamespace(ty, s->ns);

        void *ctx = PushContext(ty, s);

        switch (s->type) {
        case STATEMENT_IMPORT:
                import_module(ty, s);
                break;
        case STATEMENT_DEFER:
                if (state.func == NULL) {
                        fail(ty, "invalid defer statement (not inside of a function)");
                }
                state.func->has_defer = true;
        case STATEMENT_EXPRESSION:
        case STATEMENT_BREAK:
        case STATEMENT_NEXT:
                symbolize_expression(ty, scope, s->expression);
                break;
        case STATEMENT_CLASS_DEFINITION:
                if (!scope_locally_defined(ty, scope, s->class.name)) {
                        define_class(ty, s);
                }

                if (s->class.super != NULL) {
                        symbolize_expression(ty, scope, s->class.super);

                        if (s->class.super->symbol->class == -1)
                                fail(ty, "attempt to extend non-class");

                        class_set_super(ty, s->class.symbol, s->class.super->symbol->class);

                        for (int i = 0; i < s->class.methods.count; ++i) {
                                Expr *m = s->class.methods.items[i];
                                if (m->return_type == NULL) {
                                        Value *v = class_method(ty, s->class.super->symbol->class, m->name);
                                        if (v != NULL && v->type == VALUE_PTR) {
                                                m->return_type = ((Expr *)v->ptr)->return_type;
                                        }
                                }
                        }
                } else {
                        class_set_super(ty, s->class.symbol, 0);
                }

                subscope = scope_new(ty, s->class.name, scope, false);
                state.class = s->class.symbol;

                apply_decorator_macros(ty, subscope, s->class.methods.items, s->class.methods.count);
                apply_decorator_macros(ty, subscope, s->class.getters.items, s->class.getters.count);
                apply_decorator_macros(ty, subscope, s->class.setters.items, s->class.setters.count);
                apply_decorator_macros(ty, subscope, s->class.statics.items, s->class.statics.count);

                /*
                 * We have to move all of the operator methods out of the class and just
                 * treat them as top-level operator definitions. We want
                 *
                 *     class Foo {
                 *          <%>(other: Bar) {
                 *                  ...
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
                int n_remaining = 0;

                for (int i = 0; i < s->class.methods.count; ++i) {
                        Expr *fun = s->class.methods.items[i];
                        if (contains(OperatorCharset, *fun->name) && fun->params.count > 0) {
                                Stmt *def = NewStmt(ty, STATEMENT_OPERATOR_DEFINITION);
                                def->target = NewExpr(ty, EXPRESSION_IDENTIFIER);
                                def->target->identifier = fun->name;
                                def->value = fun;
                                def->value->is_method = false;

                                Expr *this = NewExpr(ty, EXPRESSION_IDENTIFIER);
                                this->identifier = s->class.name;

                                avI(fun->params, "self", 0);
                                avI(fun->dflts, NULL, 0);
                                avI(fun->constraints, this, 0);

                                avP(state.class_ops, def);
                        } else {
                                s->class.methods.items[n_remaining++] = fun;
                        }
                }

                s->class.methods.count = n_remaining;

                aggregate_overloads(ty, &s->class.methods, false);
                aggregate_overloads(ty, &s->class.setters, true);
                aggregate_overloads(ty, &s->class.statics, false);

                symbolize_methods(ty, subscope, s->class.methods.items, s->class.methods.count);
                symbolize_methods(ty, subscope, s->class.getters.items, s->class.getters.count);
                symbolize_methods(ty, subscope, s->class.setters.items, s->class.setters.count);
                symbolize_methods(ty, subscope, s->class.statics.items, s->class.statics.count);

                for (int i = 0; i < s->class.fields.count; ++i) {
                        Expr *field = s->class.fields.items[i];
                        switch (field->type) {
                        case EXPRESSION_IDENTIFIER:
                                symbolize_expression(ty, subscope, field->constraint);
                                break;
                        case EXPRESSION_EQ:
                                if (field->target->type != EXPRESSION_IDENTIFIER) {
                                        field = field->target;
                                        goto BadField;
                                }
                                symbolize_expression(ty, subscope, field->target->constraint);
                                break;
                        default:
                        BadField:
                                fail(ty, "invalid expression in field definition: %s", ExpressionTypeName(field));
                        }
                }

                state.class = -1;

                break;
        case STATEMENT_TAG_DEFINITION:
                if (!scope_locally_defined(ty, state.global, s->tag.name)) {
                        define_tag(ty, s);
                }

                if (s->tag.super != NULL) {
                        symbolize_expression(ty, scope, s->tag.super);
                        if (!is_tag(ty, s->tag.super))
                                fail(ty, "attempt to extend non-tag");
                }

                subscope = scope_new(ty, s->tag.name, scope, false);
                symbolize_methods(ty, subscope, s->tag.methods.items, s->tag.methods.count);
                symbolize_methods(ty, subscope, s->tag.statics.items, s->tag.statics.count);

                break;
        case STATEMENT_BLOCK:
                scope = scope_new(ty, "(block)", scope, false);

                for (size_t i = 0; i < s->statements.count; ++i) {
                        symbolize_statement(ty, scope, s->statements.items[i]);
                }

                break;
        case STATEMENT_MULTI:
                for (size_t i = 0; i < s->statements.count; ++i) {
                        symbolize_statement(ty, scope, s->statements.items[i]);
                }
                break;
        case STATEMENT_TRY:
        {
                symbolize_statement(ty, scope, s->try.s);

                for (int i = 0; i < s->try.patterns.count; ++i) {
                        Scope *catch = scope_new(ty, "(catch)", scope, false);
                        symbolize_pattern(ty, catch, s->try.patterns.items[i], NULL, true);
                        symbolize_statement(ty, catch, s->try.handlers.items[i]);
                }

                symbolize_statement(ty, scope, s->try.finally);

                break;

        }
        case STATEMENT_WHILE_MATCH:
        case STATEMENT_MATCH:
                symbolize_expression(ty, scope, s->match.e);
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        if (s->match.patterns.items[i]->type == EXPRESSION_LIST) {
                                Scope *shared = scope_new(ty, "(match-shared)", scope, false);
                                for (int j = 0; j < s->match.patterns.items[i]->es.count; ++j) {
                                        subscope = scope_new(ty, "(match-branch)", scope, false);
                                        symbolize_pattern(ty, subscope, s->match.patterns.items[i]->es.items[j], shared, true);
                                        scope_copy(ty, shared, subscope);
                                }
                                subscope = shared;
                        } else {
                                subscope = scope_new(ty, "(match-branch)", scope, false);
                                symbolize_pattern(ty, subscope, s->match.patterns.items[i], NULL, true);
                        }
                        symbolize_statement(ty, subscope, s->match.statements.items[i]);
                }
                break;
        case STATEMENT_WHILE:
                subscope = scope_new(ty, "(while)", scope, false);
                for (int i = 0; i < s->While.parts.count; ++i) {
                        struct condpart *p = s->While.parts.items[i];
                        symbolize_expression(ty, subscope, p->e);
                        symbolize_pattern(ty, subscope, p->target, NULL, p->def);
                }
                symbolize_statement(ty, subscope, s->While.block);
                break;
        case STATEMENT_IF:
                // if not let Ok(ty, x) = f() or not [y] = bar() {
                subscope = scope_new(ty, "(if)", scope, false);
                if (s->iff.neg) {
                        symbolize_statement(ty, scope, s->iff.then);
                        for (int i = 0; i < s->iff.parts.count; ++i) {
                                struct condpart *p = s->iff.parts.items[i];
                                symbolize_pattern(ty, scope, p->target, NULL, p->def);
                                symbolize_expression(ty, subscope, p->e);
                        }
                        symbolize_statement(ty, subscope, s->iff.otherwise);
                } else {
                        symbolize_statement(ty, subscope, s->iff.otherwise);
                        for (int i = 0; i < s->iff.parts.count; ++i) {
                                struct condpart *p = s->iff.parts.items[i];
                                symbolize_expression(ty, subscope, p->e);
                                symbolize_pattern(ty, subscope, p->target, NULL, p->def);

                        }
                        symbolize_statement(ty, subscope, s->iff.then);
                }
                break;
        case STATEMENT_FOR_LOOP:
                scope = scope_new(ty, "(for)", scope, false);
                symbolize_statement(ty, scope, s->for_loop.init);
                symbolize_expression(ty, scope, s->for_loop.cond);
                symbolize_expression(ty, scope, s->for_loop.next);
                symbolize_statement(ty, scope, s->for_loop.body);
                break;
        case STATEMENT_EACH_LOOP:
                symbolize_expression(ty, scope, s->each.array);
                subscope = scope_new(ty, "(for-each)", scope, false);
                symbolize_lvalue(ty, subscope, s->each.target, true, false);
                symbolize_statement(ty, subscope, s->each.body);
                symbolize_expression(ty, subscope, s->each.cond);
                symbolize_expression(ty, subscope, s->each.stop);
                break;
        case STATEMENT_RETURN:
                if (state.func == NULL) {
                        fail(ty, "invalid return statement (not inside of a function)");
                }

                for (int i = 0; i < s->returns.count; ++i) {
                    symbolize_expression(ty, scope, s->returns.items[i]);
                }

                if (state.func->type == EXPRESSION_GENERATOR) {
                        s->type = STATEMENT_GENERATOR_RETURN;
                }

                break;
        case STATEMENT_DEFINITION:
                if (s->value->type == EXPRESSION_LIST) {
                        for (int i = 0; i < s->value->es.count; ++i) {
                                symbolize_expression(ty, scope, s->value->es.items[i]);
                        }
                } else {
                        symbolize_expression(ty, scope, s->value);
                }
                symbolize_lvalue(ty, scope, s->target, true, s->pub);
                break;
        case STATEMENT_OPERATOR_DEFINITION:
                symbolize_op_def(ty, scope, s);
                break;
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
                symbolize_lvalue(ty, scope, s->target, true, s->pub);
                symbolize_expression(ty, scope, s->value);
                break;
        }

        RestoreContext(ty, ctx);
}

static void
invoke_macro(Ty *ty, Expr *e, Scope *scope)
{
        Scope *macro_scope_save = state.macro_scope;
        state.macro_scope = scope;

        Arena old = amN(1 << 20);

        symbolize_expression(ty, scope, e->macro.m);

        add_location_info(ty);
        vec_init(state.expression_locations);

        byte_vector code_save = state.code;
        vec_init(state.code);

        emit_expression(ty, e->macro.m);
        emit_instr(ty, INSTR_HALT);

        vec_init(state.expression_locations);

        vm_exec(ty, state.code.items);

        Value m = *vm_get(ty, 0);
        vmX();

        state.code = code_save;

        Value node = tyexpr(ty, e->macro.e);
        vmP(&node);

        node = vmC(&m, 1);

        state.macro_scope = macro_scope_save;

        Expr *result = cexpr(ty, &node);

        amX(old);

        symbolize_expression(ty, scope, result);

        *e = *result;
}

inline static void
patch_jumps_to(offset_vector const *js, size_t location)
{
        for (int i = 0; i < js->count; ++i) {
                int distance = location - js->items[i] - sizeof (int);
                memcpy(state.code.items + js->items[i], &distance, sizeof distance);
        }
}

inline static void
patch_loop_jumps(Ty *ty, size_t begin, size_t end)
{
        patch_jumps_to(&get_loop(ty, 0)->continues, begin);
        patch_jumps_to(&get_loop(ty, 0)->breaks, end);
}

inline static void
InitJumpGroup(JumpGroup *jg)
{
        vec_init(*jg);
        jg->label = state.label++;
}

inline static char
last_instr(void)
{
        return state.code.items[state.code.count - 1];
}

inline static void
emit_int(Ty *ty, int k)
{
        LOG("emitting int: %d", k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (int); ++i)
                avP(state.code, s[i]);
}

inline static void
emit_int16(Ty *ty, int16_t k)
{
        LOG("emitting int16_t: %d", (int)k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (int16_t); ++i)
                avP(state.code, s[i]);
}

inline static void
emit_ulong(Ty *ty, unsigned long k)
{
        LOG("emitting ulong: %lu", k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (unsigned long); ++i)
                avP(state.code, s[i]);
}

inline static void
emit_symbol(Ty *ty, uintptr_t sym)
{
        LOG("emitting symbol: %"PRIuPTR, sym);
        char const *s = (char *) &sym;
        for (int i = 0; i < sizeof (uintptr_t); ++i)
                avP(state.code, s[i]);
}

inline static void
emit_integer(Ty *ty, intmax_t k)
{

        LOG("emitting integer: %"PRIiMAX, k);
        avPn(state.code, (char const *)&k, sizeof k);
}

inline static void
emit_boolean(Ty *ty, bool b)
{

        LOG("emitting boolean: %s", b ? "true" : "false");
        char const *s = (char *) &b;
        for (int i = 0; i < sizeof (bool); ++i)
                avP(state.code, s[i]);
}

inline static void
emit_float(Ty *ty, double x)
{

        LOG("emitting float: %f", x);
        avPn(state.code, (char const *)&x, sizeof x);
}

inline static void
emit_string(Ty *ty, char const *s)
{
        LOG("emitting string: %s", s);
        avPn(state.code, s, strlen(s) + 1);
}

#ifndef TY_NO_LOG
#define emit_load_instr(ty, id, inst, i)        \
        do {                                    \
                annotate("%s", id);             \
                emit_instr(ty, inst);           \
                emit_int(ty, i);                \
                emit_string(ty, id);            \
        } while (0)
#else
#define emit_load_instr(ty, id, inst, i)        \
        do {                                    \
                annotate("%s", id);             \
                emit_instr(ty, inst);           \
                emit_int(ty, i);                \
        } while (0)
#endif

inline static void
target_captured(Ty *ty, Scope const *scope, Symbol const *s)
{
        int i = 0;
        while (scope->function->captured.items[i] != s) {
                i += 1;
        }

        emit_instr(ty, INSTR_TARGET_CAPTURED);
        emit_int(ty, i);
#ifndef TY_NO_LOG
        emit_string(ty, s->identifier);
#endif
}

inline static void
emit_load(Ty *ty, Symbol const *s, Scope const *scope)
{
        LOG("Emitting LOAD for %s", s->identifier);

        bool local = !s->global && (s->scope->function == scope->function);

        if (s->global) {
                emit_load_instr(ty, s->identifier, INSTR_LOAD_GLOBAL, s->i);
                CHECK_INIT();
        } else if (local && !s->captured) {
                emit_load_instr(ty, s->identifier, INSTR_LOAD_LOCAL, s->i);
        } else if (!local && s->captured) {
                LOG("It is captured and not owned by us");
                int i = 0;
                while (scope->function->captured.items[i] != s) {
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
        LOG("emit_tgt(ty, %s, def=%d)", s->identifier, def);

        bool local = !s->global && (s->scope->function == scope->function);

        if (s->global) {
                emit_instr(ty, INSTR_TARGET_GLOBAL);
                emit_int(ty, s->i);
        } else if (def || (local && !s->captured)) {
                emit_instr(ty, INSTR_TARGET_LOCAL);
                emit_int(ty, s->i);
        } else if (!local && s->captured) {
                target_captured(ty, scope, s);
        } else {
                emit_instr(ty, INSTR_TARGET_REF);
                emit_int(ty, s->i);
        }

        s->init = true;
}

static void
emit_list(Ty *ty, Expr const *e)
{
        emit_instr(ty, INSTR_SENTINEL);
        emit_instr(ty, INSTR_CLEAR_RC);

        if (e->type == EXPRESSION_LIST) for (int i = 0; i < e->es.count; ++i) {
                if (is_call(e->es.items[i])) {
                        emit_instr(ty, INSTR_CLEAR_RC);
                        emit_expression(ty, e->es.items[i]);
                        emit_instr(ty, INSTR_GET_EXTRA);
                } else {
                        emit_expression(ty, e->es.items[i]);
                }
        } else {
                emit_instr(ty, INSTR_CLEAR_RC);
                emit_expression(ty, e);
                emit_instr(ty, INSTR_GET_EXTRA);
        }
}

inline static JumpPlaceholder
(PLACEHOLDER_JUMP)(Ty *ty, int t)
{
        int label = state.label++;

        annotate("%sL%d%s", TERM(95), label + 1, TERM(0));

        emit_instr(ty, t);

        JumpPlaceholder jmp = {
                .off = state.code.count,
                .label = label
        };

        emit_int(ty, 0);

        return jmp;
}

inline static JumpLabel
(LABEL)(Ty *ty)
{
        JumpLabel label = {
                .off = state.code.count,
                .label = state.label++
        };

        annotate(":L%d", label.label + 1);

        return label;
}

static void
emit_constraint(Ty *ty, Expr const *c)
{
        JumpPlaceholder sc;

        emit_expression(ty, c);
        emit_instr(ty, INSTR_CHECK_MATCH);
        return;
        if (c->type == EXPRESSION_BIT_AND) {
                emit_instr(ty, INSTR_DUP);
                emit_constraint(ty, c->left);
                emit_instr(ty, INSTR_DUP);
                sc = (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF_NOT);
                emit_instr(ty, INSTR_POP);
                emit_constraint(ty, c->right);
                PATCH_JUMP(sc);
        } else if (c->type == EXPRESSION_BIT_OR) {
                emit_instr(ty, INSTR_DUP);
                emit_constraint(ty, c->left);
                emit_instr(ty, INSTR_DUP);
                sc = (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF_NOT);
                emit_instr(ty, INSTR_POP);
                emit_constraint(ty, c->right);
                PATCH_JUMP(sc);
        } else {
                emit_expression(ty, c);
                emit_instr(ty, INSTR_CHECK_MATCH);
        }
}

inline static void
align_code_to(Ty *ty, size_t n)
{
        while (((uintptr_t)(state.code.items + state.code.count)) % (alignof (int)) != ((alignof (int)) - 1))
                avP(state.code, 0x00);
        avP(state.code, 0xFF);
}

static void
add_annotation(Ty *ty, char const *name, uintptr_t start, uintptr_t end)
{
        ProgramAnnotation annotation = state.annotation;

        annotation.patched = false;
        annotation.name = name;
        annotation.module = state.filename;
        annotation.start = start;
        annotation.end = end;

        xvP(annotations, annotation);
}

static void
PatchAnnotations(Ty *ty)
{
        for (int i = 0; i < annotations.count; ++i) {
                ProgramAnnotation *annotation = vvL(annotations) - i;

                if (annotation->patched) {
                        /*
                         * We've seen all of the new annotations, everthing from here back
                         * came from an earlier module and has already been patched.
                         */
                        break;
                }

                PatchAnnotation(annotation, state.code.items);
        }
}

static void
emit_function(Ty *ty, Expr const *e, int class)
{
        /*
         * Save the current reference and bound-symbols vectors so we can
         * restore them after compiling the current function.
         */
        offset_vector selfs_save = state.selfs;
        vec_init(state.selfs);
        symbol_vector syms_save = state.bound_symbols;
        state.bound_symbols.items = e->bound_symbols.items;
        state.bound_symbols.count = e->bound_symbols.count;
        state.function_depth += 1;

        LoopStates loops = state.loops;
        vec_init(state.loops);

        TryStates tries = state.tries;
        vec_init(state.tries);

        int t_save = t;
        t = 0;

        int label_save = state.label;
        state.label = 0;

        //ProgramAnnotation annotation = state.annotation;
        //state.annotation = (ProgramAnnotation) {0};

        Scope *fs_save = state.fscope;
        state.fscope = e->scope;

        Expr *func_save = state.func;
        state.func = e;

        Symbol **caps = e->scope->captured.items;
        int *cap_indices = e->scope->cap_indices.items;
        int ncaps = e->scope->captured.count;
        int bound_caps = 0;

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
                        emit_instr(ty, INSTR_TARGET_LOCAL);
                        emit_int(ty, caps[i]->i);
                } else {
                        // FIXME: should just use same allocated variable
                        LOG("%s: Using TARGET_CAPTURED for %s: %d", e->name == NULL ? "(anon)" : e->name, caps[i]->identifier, cap_indices[i]);
                        annotate("%s", caps[i]->identifier);
                        emit_instr(ty, INSTR_TARGET_CAPTURED);
                        emit_int(ty, cap_indices[i]);
#ifndef TY_NO_LOG
                        emit_string(ty, caps[i]->identifier);
#endif
                }
        }

        emit_instr(ty, INSTR_FUNCTION);

        while (!IS_ALIGNED_FOR(int, vec_last(state.code) + 1)) {
                avP(state.code, 0);
        }

        emit_int(ty, bound_caps);

        int bound = e->scope->owned.count;

        size_t hs_offset = state.code.count;
        emit_int(ty, 0);

        size_t size_offset = state.code.count;
        emit_int(ty, 0);

        emit_int(ty, ncaps);
        emit_int(ty, bound);
        emit_int(ty, e->param_symbols.count);
        emit_int16(ty, e->rest);
        emit_int16(ty, e->ikwargs);

        for (int i = 0; i < sizeof (int) - 2 * sizeof (int16_t); ++i) {
                avP(state.code, 0);
        }

        emit_int(ty, class);

        // Need to GC code?
        avP(state.code, GetArenaAlloc(ty) != NULL);

        // Is this function hidden (i.e. omitted from stack trace messages)?
        avP(state.code, e->type == EXPRESSION_MULTI_FUNCTION);

        emit_symbol(ty, (uintptr_t)e->proto);
        emit_symbol(ty, (uintptr_t)e->doc);

#ifdef TY_ENABLE_PROFILING
        if (e->name == NULL) {
                char buffer[512];
                snprintf(
                        buffer,
                        sizeof buffer - 1,
                        "(anonymous function : %s:%d)",
                        state.filename,
                        e->start.line + 1
                );
                emit_string(ty, buffer);
        } else {
                emit_string(ty, e->name);
        }
#else
        emit_string(ty, e->name == NULL ? "(anonymous function)" : e->name);
#endif

        LOG("COMPILING FUNCTION: %s", scope_name(ty, e->scope));

        for (int i = 0; i < ncaps; ++i) {
                LOG(" => CAPTURES %s", caps[i]->identifier);
        }

        for (int i = 0; i < e->param_symbols.count; ++i) {
                emit_string(ty, e->param_symbols.items[i]->identifier);
        }

        int hs = state.code.count - hs_offset;
        memcpy(state.code.items + hs_offset, &hs, sizeof hs);

        /*
         * Remember where in the code this function's code begins so that we can compute
         * the relative offset of references to non-local variables.
         */
        size_t start_offset = state.code.count;

        for (int i = 0; i < e->param_symbols.count; ++i) {
                if (e->dflts.items[i] == NULL)
                        continue;
                Symbol const *s = e->param_symbols.items[i];
                emit_load_instr(ty, s->identifier, INSTR_LOAD_LOCAL, s->i);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NIL, need_dflt);
                PLACEHOLDER_JUMP(INSTR_JUMP, skip_dflt);
                PATCH_JUMP(need_dflt);
                annotate("%s", s->identifier);
                emit_instr(ty, INSTR_TARGET_LOCAL);
                emit_int(ty, s->i);
                emit_expression(ty, e->dflts.items[i]);
                emit_instr(ty, INSTR_ASSIGN);
                emit_instr(ty, INSTR_POP);
                PATCH_JUMP(skip_dflt);
        }

        for (int i = 0; i < e->param_symbols.count; ++i) {
                if (e->constraints.items[i] == NULL || (!e->is_overload && !CheckConstraints))
                        continue;
                Symbol const *s = e->param_symbols.items[i];
                size_t start = state.code.count;
                emit_load_instr(ty, s->identifier, INSTR_LOAD_LOCAL, s->i);
                emit_constraint(ty, e->constraints.items[i]);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF, good);
                if (e->is_overload) {
                        emit_instr(ty, INSTR_POP);
                        emit_instr(ty, INSTR_NONE);
                        emit_instr(ty, INSTR_RETURN);
                } else {
                        emit_load_instr(ty, s->identifier, INSTR_LOAD_LOCAL, s->i);
                        emit_instr(ty, INSTR_BAD_CALL);
                        if (e->name != NULL)
                                emit_string(ty, e->name);
                        else
                                emit_string(ty, "(anonymous function)");
                        emit_string(ty, e->param_symbols.items[i]->identifier);
                        add_location(ty, e->constraints.items[i], start, state.code.count);
                }
                emit_instr(ty, INSTR_POP);
                PATCH_JUMP(good);
        }

        int function_resources = state.function_resources;
        state.function_resources = state.resources;

        Stmt *body = e->body;
        Stmt try;
        Stmt cleanup;

        if (e->has_defer) {
                try.type = STATEMENT_TRY_CLEAN;
                try.start = body->start;
                try.end = body->end;
                try.try.s = body;
                vec_init(try.try.patterns);
                vec_init(try.try.handlers);

                cleanup.type = STATEMENT_CLEANUP;
                cleanup.start = body->start;
                cleanup.end = body->end;

                try.try.finally = &cleanup;

                body = &try;
        }

        if (e->type == EXPRESSION_GENERATOR) {
                emit_instr(ty, INSTR_MAKE_GENERATOR);
                emit_statement(ty, body, false);
                LABEL(end);
                emit_instr(ty, INSTR_TAG);
                emit_int(ty, TAG_NONE);
                emit_instr(ty, INSTR_YIELD);
                emit_instr(ty, INSTR_POP);
                JUMP(end);
                patch_jumps_to(&state.generator_returns, end.off);
        } else if (e->type == EXPRESSION_MULTI_FUNCTION) {
                for (int i = 0; i < e->functions.count; ++i) {
                        if (!e->is_method) {
                                emit_instr(ty, INSTR_SAVE_STACK_POS);
                                emit_load_instr(ty, "@", INSTR_LOAD_LOCAL, 0);
                                emit_spread(ty, NULL, false);
                                emit_load_instr(ty, "", INSTR_LOAD_GLOBAL, ((Stmt *)e->functions.items[i])->target->symbol->i);
                                CHECK_INIT();
                                emit_instr(ty, INSTR_CALL);
                                emit_int(ty, -1);
                                emit_int(ty, 0);
                                emit_instr(ty, INSTR_RETURN_IF_NOT_NONE);
                                emit_instr(ty, INSTR_POP);
                        } else if (e->mtype == MT_SET) {
                                emit_load_instr(ty, "@", INSTR_LOAD_LOCAL, 0);
                                emit_load_instr(ty, "self", INSTR_LOAD_LOCAL, 1);
                                emit_instr(ty, INSTR_TARGET_MEMBER);
                                emit_int(ty, M_ID(e->functions.items[i]->name));
                                emit_instr(ty, INSTR_ASSIGN);
                                emit_instr(ty, INSTR_RETURN_IF_NOT_NONE);
                                emit_instr(ty, INSTR_POP);
                        } else {
                                emit_instr(ty, INSTR_SAVE_STACK_POS);
                                emit_load_instr(ty, "@", INSTR_LOAD_LOCAL, 0);
                                emit_spread(ty, NULL, false);
                                emit_load_instr(ty, "self", INSTR_LOAD_LOCAL, 1);
                                emit_instr(ty, INSTR_CALL_METHOD);
                                emit_int(ty, -1);
                                emit_int(ty, M_ID(e->functions.items[i]->name));
                                emit_int(ty, 0);
                                emit_instr(ty, INSTR_RETURN_IF_NOT_NONE);
                                emit_instr(ty, INSTR_POP);
                        }
                }
                emit_instr(ty, INSTR_BAD_DISPATCH);
        } else {
                for (int i = ncaps - 1; i >= 0; --i) {
                        if (caps[i]->scope->function == e->scope) {
                                emit_instr(ty, INSTR_CAPTURE);
                                emit_int(ty, caps[i]->i);
                                emit_int(ty, i);
                        }
                }
                emit_statement(ty, body, true);
                if (CheckConstraints && e->return_type != NULL) {
                        emit_return_check(ty, e);
                }
                emit_instr(ty, INSTR_RETURN);
        }

        state.function_resources = function_resources;

        // TODO: what to do here?
        //add_annotation(ty, e->proto, start_offset, state.code.count);

        int bytes = state.code.count - start_offset;
        memcpy(state.code.items + size_offset, &bytes, sizeof bytes);
        LOG("bytes in func = %d", bytes);

        int self_cap = -1;

        for (int i = 0; i < ncaps; ++i) {
                if (caps[i]->scope->function == e->scope)
                        continue;
                if (caps[i] == e->function_symbol) {
                        LOG("Function '%s' self-captures at i=%d", e->name == NULL ? "(anon)" : e->name, i);
                        self_cap = i;
                }
                bool local = caps[i]->scope->function == fs_save;
                LOG("local(%s, %s): %d", e->name == NULL ? "(anon)" : e->name, caps[i]->identifier, local);
                LOG("  fscope(%s) = %p, fs_save = %p", caps[i]->identifier, caps[i]->scope->function, fs_save);
                emit_boolean(ty, local);
                emit_int(ty, i);
        }

        //state.annotation = annotation;
        state.label = label_save;
        state.fscope = fs_save;
        state.selfs = selfs_save;
        state.bound_symbols = syms_save;
        state.function_depth -= 1;
        state.loops = loops;
        state.tries = tries;
        t = t_save;

        LOG("state.fscope: %s", scope_name(ty, state.fscope));

        if (e->function_symbol != NULL) {
                emit_tgt(ty, e->function_symbol, e->scope->parent, false);
                emit_instr(ty, INSTR_ASSIGN);
        }

        if (self_cap != -1) {
                emit_instr(ty, INSTR_PATCH_ENV);
                emit_int(ty, self_cap);
        }

        state.func = func_save;

        for (int i = 0; i < e->decorators.count; ++i) {
                Expr *c = e->decorators.items[i];
                if (c->type == EXPRESSION_FUNCTION_CALL) {
                        avI(c->args, NULL, 0);
                        avI(c->fconds, NULL, 0);
                } else if (c->type == EXPRESSION_METHOD_CALL) {
                        avI(c->method_args, NULL, 0);
                        avI(c->mconds, NULL, 0);
                } else {
                        fail(ty, "bro?");
                }
                emit_expression(ty, c);
        }
}

static void
emit_and(Ty *ty, Expr const *left, Expr const *right)
{
        emit_expression(ty, left);
        emit_instr(ty, INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, left_false);

        emit_instr(ty, INSTR_POP);
        emit_expression(ty, right);

        PATCH_JUMP(left_false);
}

static void
emit_or(Ty *ty, Expr const *left, Expr const *right)
{
        emit_expression(ty, left);
        emit_instr(ty, INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF, left_true);

        emit_instr(ty, INSTR_POP);
        emit_expression(ty, right);

        PATCH_JUMP(left_true);
}

static void
emit_coalesce(Ty *ty, Expr const *left, Expr const *right)
{
        emit_expression(ty, left);
        emit_instr(ty, INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NIL, left_nil);
        PLACEHOLDER_JUMP(INSTR_JUMP, left_good);

        PATCH_JUMP(left_nil);

        emit_instr(ty, INSTR_POP);
        emit_expression(ty, right);

        PATCH_JUMP(left_good);
}

static void
emit_special_string(Ty *ty, Expr const *e)
{
        int n = e->expressions.count;

        if (e->strings.items[0][0] != '\0') {
                emit_instr(ty, INSTR_STRING);
                emit_string(ty, e->strings.items[0]);
                n += 1;
        }

        for (int i = 1; i < e->strings.count; ++i) {
                if (e->strings.items[i][0] != '\0') {
                        n += 1;
                }
        }

        for (int i = 0; i < e->expressions.count; ++i) {
                char const *fmt = *v_(e->fmts, i);
                Expr const *arg = *v_(e->fmt_args, i);
                Expr const *ex = *v_(e->expressions, i);
                int width = *v_(e->widths, i);

                if (fmt == NULL) {
                        emit_expression(ty, ex);
                        emit_instr(ty, INSTR_TO_STRING);
                } else if (arg == NULL ) {
                        emit_expression(ty, ex);
                        emit_instr(ty, INSTR_FMT1);
                        emit_string(ty, fmt);
                        emit_int(ty, width);
                } else {
                        emit_expression(ty, arg);
                        emit_expression(ty, ex);
                        emit_instr(ty, INSTR_FMT2);
                        emit_string(ty, fmt);
                        emit_int(ty, width);
                }

                if (e->strings.items[i + 1][0] != '\0') {
                        emit_instr(ty, INSTR_STRING);
                        emit_string(ty, e->strings.items[i + 1]);
                }
        }

        if (n > 1) {
                emit_instr(ty, INSTR_CONCAT_STRINGS);
                emit_int(ty, n);
        } else if (n == 0) {
                emit_instr(ty, INSTR_STRING);
                avP(state.code, '\0');
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
        if (state.function_depth == 0) {
                fail(ty, "invalid yield expression (not inside of a function)");
        }

        if (n > 1) {
                fail(ty, "yielding multiple values isn't implemented yet");
        }

        for (int i = 0; i < n; ++i) {
                emit_expression(ty, es[i]);
                if (wrap) {
                        emit_instr(ty, INSTR_TAG_PUSH);
                        emit_int(ty, TAG_SOME);
                }
        }

        emit_instr(ty, INSTR_YIELD);
}

static void
emit_return_check(Ty *ty, Expr const *f)
{
        size_t start = state.code.count;

        emit_instr(ty, INSTR_DUP);
        emit_constraint(ty, f->return_type);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF, good);
        emit_instr(ty, INSTR_BAD_CALL);

        if (f->name != NULL)
                emit_string(ty, f->name);
        else
                emit_string(ty, "(anonymous function)");

        emit_string(ty, "return value");

        add_location(ty, f->return_type, start, state.code.count);

        PATCH_JUMP(good);
}

static bool
emit_return(Ty *ty, Stmt const *s)
{
        if (inside_finally(ty)) {
                fail(ty, "invalid return statement (occurs in a finally block)");
        }

        /* returning from within a for-each loop must be handled specially */
        for (int i = 0; i < state.loops.count; ++i) {
                if (get_loop(ty, i)->each) {
                        emit_instr(ty, INSTR_POP);
                        emit_instr(ty, INSTR_POP);
                }
        }

        Expr **rets = s->returns.items;
        int nret = s->returns.count;

        bool tco = (nret == 1)
                && (state.tries.count == 0)
                && (state.function_resources == state.resources)
                && (!CheckConstraints || state.func->return_type == NULL)
                && is_call(rets[0])
                && !is_variadic(rets[0])
                && (rets[0]->function->type == EXPRESSION_IDENTIFIER)
                && (rets[0]->function->symbol == state.func->function_symbol)
                && (rets[0]->args.count == state.func->params.count)
                && (rets[0]->kwargs.count == 0);

        if (tco) {
                for (int i = 0; i < rets[0]->args.count; ++i) {
                        emit_expression(ty, rets[0]->args.items[i]);
                }

                emit_instr(ty, INSTR_TAIL_CALL);

                return true;
        }

        if (s->returns.count > 0 ) for (int i = 0; i < s->returns.count; ++i) {
                emit_expression(ty, s->returns.items[i]);
        } else {
                emit_instr(ty, INSTR_NIL);
        }

        if (state.tries.count > 0) {
                emit_instr(ty, INSTR_FINALLY);
        }

        for (int i = state.function_resources; i < state.resources; ++i) {
                emit_instr(ty, INSTR_DROP);
        }

        if (CheckConstraints && state.func->return_type != NULL) {
                emit_return_check(ty, state.func);
        }

        if (s->returns.count > 1) {
                emit_instr(ty, INSTR_MULTI_RETURN);
                emit_int(ty, (int)s->returns.count - 1);
        } else {
                emit_instr(ty, INSTR_RETURN);
        }

        return true;
}

static bool
emit_try(Ty *ty, Stmt const *s, bool want_result)
{
        emit_instr(ty, INSTR_TRY);

        size_t catch_offset = state.code.count;
        emit_int(ty, 0);

        size_t finally_offset = state.code.count;
        emit_int(ty, -1);

        size_t end_offset = state.code.count;
        emit_int(ty, -1);

        begin_try(ty);

        if (s->type == STATEMENT_TRY_CLEAN) {
                emit_instr(ty, INSTR_PUSH_DEFER_GROUP);
        }

        bool returns = emit_statement(ty, s->try.s, want_result);

        PLACEHOLDER_JUMP(INSTR_JUMP, end);

        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        PATCH_OFFSET(catch_offset);

        for (int i = 0; i < s->try.patterns.count; ++i) {
                returns &= emit_catch(ty, s->try.patterns.items[i], NULL, s->try.handlers.items[i], want_result);
        }

        emit_instr(ty, INSTR_FINALLY);
        emit_instr(ty, INSTR_RETHROW);

        patch_jumps_to(&state.match_successes, state.code.count);
        PATCH_JUMP(end);

        state.match_successes = successes_save;

        emit_instr(ty, INSTR_FINALLY);

        if (s->try.finally != NULL) {
                PLACEHOLDER_JUMP(INSTR_JUMP, end_real);
                PATCH_OFFSET(finally_offset);
                begin_finally(ty);
                returns &= emit_statement(ty, s->try.finally, false);
                end_finally(ty);
                PATCH_OFFSET(end_offset);
                emit_instr(ty, INSTR_HALT);
                PATCH_JUMP(end_real);
        } else {
                returns = false;
        }

        end_try(ty);

        return returns;
}

static void
emit_for_loop(Ty *ty, Stmt const *s, bool want_result)
{
        begin_loop(ty, want_result, false);

        if (s->for_loop.init != NULL)
                emit_statement(ty, s->for_loop.init, false);

        PLACEHOLDER_JUMP(INSTR_JUMP, skip_next);

        LABEL(begin);

        if (s->for_loop.next != NULL) {
                emit_expression(ty, s->for_loop.next);
                emit_instr(ty, INSTR_POP);
        }

        PATCH_JUMP(skip_next);

        JumpPlaceholder end_jump;
        if (s->for_loop.cond != NULL) {
                emit_expression(ty, s->for_loop.cond);
                end_jump = (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF_NOT);
        }

        emit_statement(ty, s->for_loop.body, false);

        JUMP(begin);

        if (s->for_loop.cond != NULL)
                PATCH_JUMP(end_jump);

        if (want_result)
                emit_instr(ty, INSTR_NIL);

        patch_loop_jumps(ty, begin.off, state.code.count);

        end_loop(ty);
}

static bool
has_any_names(Expr const *e)
{
        for (int i = 0; i < e->names.count; ++i) {
                if (e->names.items[i] != NULL) {
                        return true;
                }
        }

        return false;
}

static void
emit_record_rest(Ty *ty, Expr const *rec, int i, bool is_assignment)
{
        emit_tgt(ty, rec->es.items[i]->symbol, state.fscope, true);

        size_t bad_assign_jump;

        if (!is_assignment) {
                FAIL_MATCH_IF(RECORD_REST);
        } else {
                emit_instr(ty, INSTR_RECORD_REST);
                bad_assign_jump = state.code.count;
                emit_int(ty, 0);
        }

        while (!IS_ALIGNED_FOR(int, vec_last(state.code) + 1)) {
                avP(state.code, 0);
        }

        for (int j = 0; j < i; ++j) {
                if (rec->names.items[j] != NULL) {
                        emit_int(ty, intern(&xD.members, rec->names.items[j])->id);
                }
        }

        emit_int(ty, -1);

        if (is_assignment) {
                emit_instr(ty, INSTR_JUMP);
                emit_int(ty, 1);
                PATCH_OFFSET(bad_assign_jump);
                emit_instr(ty, INSTR_BAD_MATCH);
        }
}

static void
emit_try_match_(Ty *ty, Expr const *pattern)
{
        size_t start = state.code.count;
        bool need_loc = false;
        bool set = true;
        bool after = false;

        switch (pattern->type) {
        case EXPRESSION_MATCH_ANY:
                break;
        case EXPRESSION_RESOURCE_BINDING:
                emit_instr(ty, INSTR_PUSH_DROP);
                /* fallthrough */
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_ALIAS_PATTERN:
                if (strcmp(pattern->identifier, "_") == 0) {
                        /* nothing to do */
                } else {
                        emit_tgt(ty, pattern->symbol, state.fscope, true);
                        emit_instr(ty, INSTR_ASSIGN);
                }
                if (pattern->constraint != NULL) {
                        emit_instr(ty, INSTR_DUP);
                        emit_constraint(ty, pattern->constraint);
                        FAIL_MATCH_IF(JUMP_IF_NOT);
                }
                if (pattern->type == EXPRESSION_ALIAS_PATTERN) {
                        emit_try_match_(ty, pattern->aliased);
                }
                break;
        case EXPRESSION_TAG_PATTERN:
                emit_tgt(ty, pattern->symbol, state.fscope, true);
                FAIL_MATCH_IF(TRY_STEAL_TAG);
                emit_try_match_(ty, pattern->tagged);
                break;
        case EXPRESSION_CHECK_MATCH:
                emit_try_match_(ty, pattern->left);
                emit_instr(ty, INSTR_DUP);
                emit_constraint(ty, pattern->right);
                FAIL_MATCH_IF(JUMP_IF_NOT);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_tgt(ty, pattern->symbol, state.fscope, true);
                FAIL_MATCH_IF(TRY_ASSIGN_NON_NIL);
                break;
        case EXPRESSION_MUST_EQUAL:
                emit_load(ty, pattern->symbol, state.fscope);
                FAIL_MATCH_IF(ENSURE_EQUALS_VAR);
                need_loc = true;
                break;
        case EXPRESSION_KW_AND:
                emit_try_match_(ty, pattern->left);
                for (int i = 0; i < pattern->p_cond.count; ++i) {
                        struct condpart *p = pattern->p_cond.items[i];
                        emit_expression(ty, p->e);
                        if (p->target == NULL) {
                                FAIL_MATCH_IF(JUMP_IF_NOT);
                        } else {
                                emit_try_match_(ty, p->target);
                                emit_instr(ty, INSTR_POP);
                        }
                }
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                emit_instr(ty, INSTR_DUP);
                FAIL_MATCH_IF(JUMP_IF_NIL);
                // Fallthrough
        case EXPRESSION_VIEW_PATTERN:
                emit_instr(ty, INSTR_DUP);
                emit_expression(ty, pattern->left);
                emit_instr(ty, INSTR_CALL);
                emit_int(ty, 1);
                emit_int(ty, 0);
                add_location(ty, pattern->left, start, state.code.count);
                emit_try_match_(ty, pattern->right);
                emit_instr(ty, INSTR_POP);
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < pattern->elements.count; ++i) {
                        if (pattern->elements.items[i]->type == EXPRESSION_MATCH_REST) {
                                if (after) {
                                        PushContext(ty, pattern->elements.items[i]);
                                        fail(ty, "array pattern cannot contain multiple gather elements");
                                } else {
                                        after = true;
                                }
                                emit_tgt(ty, pattern->elements.items[i]->symbol, state.fscope, true);
                                FAIL_MATCH_IF(ARRAY_REST);
                                emit_int(ty, i);
                                emit_int(ty, pattern->elements.count - i - 1);
                        } else {
                                FAIL_MATCH_IF(TRY_INDEX);
                                if (after) {
                                        if (pattern->optional.items[i]) {
                                                PushContext(ty, pattern->elements.items[i]);
                                                fail(ty, "optional element cannot come after a gather element in array pattern");
                                        }
                                        emit_int(ty, i - pattern->elements.count);
                                } else {
                                        emit_int(ty, i);
                                }
                                emit_boolean(ty, !pattern->optional.items[i]);

                                emit_try_match_(ty, pattern->elements.items[i]);

                                emit_instr(ty, INSTR_POP);
                        }
                }

                if (!after) {
                        FAIL_MATCH_IF(ENSURE_LEN);
                        emit_int(ty, pattern->elements.count);
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
                for (int i = 0; i < pattern->keys.count; ++i) {
                        if (pattern->values.items[i] != NULL) {
                                set = false;
                                break;
                        }
                }
                if (set) {
                        emit_expression(ty, pattern);
                        FAIL_MATCH_IF(ENSURE_SAME_KEYS);
                } else {
                        FAIL_MATCH_IF(ENSURE_DICT);
                        for (int i = 0; i < pattern->keys.count; ++i) {
                                if (pattern->values.items[i] != NULL) {
                                        emit_instr(ty, INSTR_DUP);
                                        emit_expression(ty, pattern->keys.items[i]);
                                        emit_instr(ty, INSTR_SUBSCRIPT);
                                        emit_try_match_(ty, pattern->values.items[i]);
                                        emit_instr(ty, INSTR_POP);
                                } else {
                                        emit_expression(ty, pattern->keys.items[i]);
                                        FAIL_MATCH_IF(ENSURE_CONTAINS);
                                }
                        }
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_instr(ty, INSTR_DUP);
                FAIL_MATCH_IF(TRY_TAG_POP);
                emit_int(ty, tag_app_tag(pattern));

                emit_try_match_(ty, pattern->tagged);

                emit_instr(ty, INSTR_POP);
                break;
        case EXPRESSION_REGEX:
                emit_tgt(ty, pattern->match_symbol, state.fscope, true);
                FAIL_MATCH_IF(TRY_REGEX);
                emit_symbol(ty, (uintptr_t) pattern->regex);
                need_loc = true;
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < pattern->es.count; ++i) {
                        if (pattern->es.items[i]->type == EXPRESSION_MATCH_REST) {
                                if (has_any_names(pattern)) {
                                        emit_record_rest(ty, pattern, i, false);
                                } else {
                                        emit_tgt(ty, pattern->es.items[i]->symbol, state.fscope, true);
                                        FAIL_MATCH_IF(TUPLE_REST);
                                        emit_int(ty, i);

                                        if (i + 1 != pattern->es.count)
                                                fail(ty, "the *<id> tuple-matching pattern must be the last pattern in the tuple");
                                }
                        } else if (pattern->names.items[i] != NULL) {
                                FAIL_MATCH_IF(TRY_TUPLE_MEMBER);
                                emit_boolean(ty, pattern->required.items[i]);
                                emit_int(ty, M_ID(pattern->names.items[i]));
                                emit_try_match_(ty, pattern->es.items[i]);
                                emit_instr(ty, INSTR_POP);
                        } else {
                                FAIL_MATCH_IF(TRY_INDEX_TUPLE);
                                emit_int(ty, i);
                                emit_try_match_(ty, pattern->es.items[i]);
                                emit_instr(ty, INSTR_POP);
                        }
                }

                if (pattern->es.count == 0 || pattern->es.items[pattern->es.count - 1]->type != EXPRESSION_MATCH_REST) {
                        FAIL_MATCH_IF(ENSURE_LEN_TUPLE);
                        emit_int(ty, pattern->es.count);
                }

                break;
        case EXPRESSION_LIST:
        {
                vec(JumpPlaceholder) matched = {0};

                for (int i = 0; i < pattern->es.count; ++i) {
                        JumpGroup fails_save = state.match_fails;
                        InitJumpGroup(&state.match_fails);

                        emit_try_match_(ty, pattern->es.items[i]);
                        avP(matched, (PLACEHOLDER_JUMP)(ty, INSTR_JUMP));

                        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
                        patch_jumps_to(&state.match_fails, state.code.count);

                        state.match_fails = fails_save;
                }

                emit_instr(ty, INSTR_BAD_MATCH);

                for (int i = 0; i < matched.count; ++i) {
                        PATCH_JUMP(matched.items[i]);
                }

                break;
        }
        default:
                /*
                 * Need to think about how this should work...
                 */
                emit_instr(ty, INSTR_DUP);
                emit_expression(ty, pattern);
                //emit_instr(ty, INSTR_CHECK_MATCH);
                emit_instr(ty, INSTR_EQ);
                FAIL_MATCH_IF(JUMP_IF_NOT);
                need_loc = true;
        }

        if (KEEP_LOCATION(pattern) || need_loc)
                add_location(ty, pattern, start, state.code.count);
}

static void
emit_try_match(Ty *ty, Expr const *pattern)
{
        emit_try_match_(ty, pattern);
}

static bool
emit_catch(Ty *ty, Expr const *pattern, Expr const *cond, Stmt const *s, bool want_result)
{
        JumpGroup fails_save = state.match_fails;

        InitJumpGroup(&state.match_fails);

        emit_instr(ty, INSTR_SAVE_STACK_POS);
        emit_try_match(ty, pattern);

        if (cond != NULL) {
                emit_expression(ty, cond);
                FAIL_MATCH_IF(JUMP_IF_NOT);
        }

        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        emit_instr(ty, INSTR_CLEAR_EXTRA);

        bool returns = false;

        emit_instr(ty, INSTR_CATCH);

        if (s != NULL) {
                returns = emit_statement(ty, s, want_result);
        } else if (want_result) {
                emit_instr(ty, INSTR_NIL);
        }

        emit_instr(ty, INSTR_RESUME_TRY);

        emit_instr(ty, INSTR_JUMP);
        avP(state.match_successes, state.code.count);
        emit_int(ty, 0);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);

        emit_instr(ty, INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;

        return returns;
}

static bool
emit_case(Ty *ty, Expr const *pattern, Expr const *cond, Stmt const *s, bool want_result)
{
        if (pattern->type == EXPRESSION_LIST) {
                bool returns = false;
                for (int i = 0; i < pattern->es.count; ++i) {
                        returns = emit_case(ty, pattern->es.items[i], NULL, s, want_result);
                }
                return returns;
        }

        JumpGroup fails_save = state.match_fails;
        InitJumpGroup(&state.match_fails);

        if (pattern->has_resources) {
                emit_instr(ty, INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        emit_instr(ty, INSTR_SAVE_STACK_POS);
        emit_try_match(ty, pattern);

        if (cond != NULL) {
                emit_expression(ty, cond);
                FAIL_MATCH_IF(JUMP_IF_NOT);
        }

        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        emit_instr(ty, INSTR_CLEAR_EXTRA);

        bool returns = false;

        if (s != NULL) {
                returns = emit_statement(ty, s, want_result);
        } else if (want_result) {
                emit_instr(ty, INSTR_NIL);
        }

        if (pattern->has_resources) {
                emit_instr(ty, INSTR_DROP);
                state.resources -= 1;
        }

        emit_instr(ty, INSTR_JUMP);
        avP(state.match_successes, state.code.count);
        emit_int(ty, 0);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;

        return returns;
}

static void
emit_expression_case(Ty *ty, Expr const *pattern, Expr const *e)
{
        if (pattern->type == EXPRESSION_LIST) {
                for (int i = 0; i < pattern->es.count; ++i) {
                        emit_expression_case(ty, pattern->es.items[i], e);
                }
                return;
        }

        JumpGroup fails_save = state.match_fails;
        InitJumpGroup(&state.match_fails);

        if (pattern->has_resources) {
                emit_instr(ty, INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        emit_instr(ty, INSTR_SAVE_STACK_POS);
        emit_try_match(ty, pattern);

        /*
         * Go back to where the subject of the match is on top of the stack,
         * then pop it and execute the code to produce the result of this branch.
         */
        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        emit_instr(ty, INSTR_CLEAR_EXTRA);
        emit_expression(ty, e);
        if (pattern->has_resources) {
                emit_instr(ty, INSTR_DROP);
                state.resources -= 1;
        }

        /*
         * We've successfully matched a pattern+condition and produced a result, so we jump
         * to the end of the match expression. i.e., there is no fallthrough.
         */
        emit_instr(ty, INSTR_JUMP);
        avP(state.match_successes, state.code.count);
        emit_int(ty, 0);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;
}

static bool
emit_match_statement(Ty *ty, Stmt const *s, bool want_result)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        /* FIXME: Why do we need a sentinel here? */
        emit_instr(ty, INSTR_SENTINEL);
        emit_instr(ty, INSTR_CLEAR_RC);
        emit_expression(ty, s->match.e);

        bool returns = true;

        for (int i = 0; i < s->match.patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                returns &= emit_case(ty, s->match.patterns.items[i], NULL, s->match.statements.items[i], want_result);
        }

        /*
         * Nothing matched. This is a runtime errror.
         */
        emit_instr(ty, INSTR_BAD_MATCH);

        patch_jumps_to(&state.match_successes, state.code.count);
        state.match_successes = successes_save;

        return returns;
}

static void
emit_while_match(Ty *ty, Stmt const *s, bool want_result)
{
        begin_loop(ty, want_result, false);

        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        LABEL(begin);

        emit_list(ty, s->match.e);
        emit_instr(ty, INSTR_FIX_EXTRA);

        for (int i = 0; i < s->match.patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                emit_case(ty, s->match.patterns.items[i], NULL, s->match.statements.items[i], false);
        }

        /*
         * If nothing matches, we jump out of the loop.
         */
        emit_instr(ty, INSTR_CLEAR_EXTRA);
        PLACEHOLDER_JUMP(INSTR_JUMP, finished);

        /*
         * Something matched, so we iterate again.
         */
        patch_jumps_to(&state.match_successes, state.code.count);
        JUMP(begin);

        PATCH_JUMP(finished);

        if (want_result)
                emit_instr(ty, INSTR_NIL);

        patch_loop_jumps(ty, begin.off, state.code.count);

        state.match_successes = successes_save;

        end_loop(ty);
}

static bool
emit_while(Ty *ty, Stmt const *s, bool want_result)
{
        begin_loop(ty, want_result, false);

        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        JumpGroup fails_save = state.match_fails;
        InitJumpGroup(&state.match_fails);

        LABEL(start);

        bool has_resources = false;

        bool simple = is_simple_condition(&s->iff.parts);

        for (int i = 0; i < s->While.parts.count; ++i) {
                struct condpart *p = s->While.parts.items[i];
                if (simple) {
                        emit_expression(ty, p->e);
                        FAIL_MATCH_IF(JUMP_IF_NOT);
                } else if (p->target == NULL) {
                        emit_instr(ty, INSTR_SAVE_STACK_POS);
                        emit_expression(ty, p->e);
                        FAIL_MATCH_IF(JUMP_IF_NOT);
                        emit_instr(ty, INSTR_RESTORE_STACK_POS);
                } else {
                        if (p->target->has_resources && !has_resources) {
                                emit_instr(ty, INSTR_PUSH_DROP_GROUP);
                                state.resources += 1;
                                has_resources = true;
                        }
                        emit_instr(ty, INSTR_SAVE_STACK_POS);
                        emit_list(ty, p->e);
                        emit_instr(ty, INSTR_FIX_EXTRA);
                        emit_try_match(ty, p->target);
                        emit_instr(ty, INSTR_RESTORE_STACK_POS);
                }
        }

        emit_statement(ty, s->While.block, false);

        if (has_resources) {
                emit_instr(ty, INSTR_DROP);
                state.resources -= 1;
        }

        JUMP(start);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);
        if (!simple) emit_instr(ty, INSTR_RESTORE_STACK_POS);

        if (want_result) {
                emit_instr(ty, INSTR_NIL);
        }

        patch_loop_jumps(ty, start.off, state.code.count);

        end_loop(ty);

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        return false;
}

static bool
emit_if_not(Ty *ty, Stmt const *s, bool want_result)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        JumpGroup fails_save = state.match_fails;
        InitJumpGroup(&state.match_fails);

        bool has_resources = false;

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (p->target != NULL && p->target->has_resources) {
                        has_resources = true;
                        break;
                }
        }

        if (has_resources) {
                emit_instr(ty, INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        bool simple = is_simple_condition(&s->iff.parts);

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (simple) {
                        emit_expression(ty, p->e);
                        FAIL_MATCH_IF(JUMP_IF);
                } else if (p->target == NULL) {
                        emit_instr(ty, INSTR_SAVE_STACK_POS);
                        emit_expression(ty, p->e);
                        FAIL_MATCH_IF(JUMP_IF);
                        emit_instr(ty, INSTR_RESTORE_STACK_POS);
                } else {
                        emit_instr(ty, INSTR_SAVE_STACK_POS);
                        emit_list(ty, p->e);
                        emit_instr(ty, INSTR_FIX_EXTRA);
                        emit_try_match(ty, p->target);
                        emit_instr(ty, INSTR_RESTORE_STACK_POS);
                }
        }

        bool returns = false;

        if (s->iff.otherwise != NULL) {
                returns |= emit_statement(ty, s->iff.otherwise, want_result);
        } else if (want_result) {
                emit_instr(ty, INSTR_NIL);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, done);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);
        if (!simple) emit_instr(ty, INSTR_RESTORE_STACK_POS);

        returns &= emit_statement(ty, s->iff.then, want_result);

        PATCH_JUMP(done);

        if (has_resources) {
                emit_instr(ty, INSTR_DROP);
                state.resources -= 1;
        }

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        return returns;
}

static bool
emit_if(Ty *ty, Stmt const *s, bool want_result)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        /* Special case for 'if not' */
        if (s->iff.neg) {
                struct condpart *p = s->iff.parts.items[0];

                emit_list(ty, p->e);
                emit_instr(ty, INSTR_FIX_EXTRA);

                bool returns = emit_case(ty, p->target, NULL, s->iff.otherwise, want_result);
                emit_instr(ty, INSTR_CLEAR_EXTRA);
                returns &= emit_statement(ty, s->iff.then, want_result);

                patch_jumps_to(&state.match_successes, state.code.count);
                state.match_successes = successes_save;

                return returns;
        }

        JumpGroup fails_save = state.match_fails;
        InitJumpGroup(&state.match_fails);

        bool has_resources = false;

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (p->target != NULL && p->target->has_resources) {
                        has_resources = true;
                        break;
                }
        }

        if (has_resources) {
                emit_instr(ty, INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        bool simple = is_simple_condition(&s->iff.parts);

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (simple) {
                        emit_expression(ty, p->e);
                        FAIL_MATCH_IF(JUMP_IF_NOT);
                } else if (p->target == NULL) {
                        emit_instr(ty, INSTR_SAVE_STACK_POS);
                        emit_expression(ty, p->e);
                        FAIL_MATCH_IF(JUMP_IF_NOT);
                        emit_instr(ty, INSTR_RESTORE_STACK_POS);
                } else {
                        emit_instr(ty, INSTR_SAVE_STACK_POS);
                        emit_list(ty, p->e);
                        emit_instr(ty, INSTR_FIX_EXTRA);
                        emit_try_match(ty, p->target);
                        emit_instr(ty, INSTR_RESTORE_STACK_POS);
                }
        }

        bool returns = emit_statement(ty, s->iff.then, want_result);
        PLACEHOLDER_JUMP(INSTR_JUMP, done);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);
        if (!simple) emit_instr(ty, INSTR_RESTORE_STACK_POS);

        if (s->iff.otherwise != NULL) {
                returns &= emit_statement(ty, s->iff.otherwise, want_result);
        } else {
                if (want_result) {
                        emit_instr(ty, INSTR_NIL);
                }
                returns = false;
        }

        PATCH_JUMP(done);

        if (has_resources) {
                emit_instr(ty, INSTR_DROP);
                state.resources -= 1;
        }

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        return returns;
}

static void
emit_match_expression(Ty *ty, Expr const *e)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        /*
         * FIXME:
         *
         * We used to use emit_list here, but matching on multiple return values
         * was never used and could cause some problems for the GC.
         *
         * However, I don't know if/why SENTINEL is really needed here still.
         *
         * This applies to emit_match_statement(ty) as well.
         */
        emit_instr(ty, INSTR_SENTINEL);
        emit_instr(ty, INSTR_CLEAR_RC);
        emit_expression(ty, e->subject);

        for (int i = 0; i < e->patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                emit_expression_case(ty, e->patterns.items[i], e->thens.items[i]);
        }

        /*
         * Nothing matched. This is a runtime errror.
         */
        emit_instr(ty, INSTR_BAD_MATCH);

        /*
         * If a branch matched successfully, it will jump to this point
         * after it is evaluated so as not to fallthrough to the other
         * branches.
         */
        patch_jumps_to(&state.match_successes, state.code.count);

        state.match_successes = successes_save;
}

static void
emit_target(Ty *ty, Expr *target, bool def)
{
        size_t start = state.code.count;

        switch (target->type) {
        case EXPRESSION_RESOURCE_BINDING:
                emit_instr(ty, INSTR_PUSH_DROP);
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_ANY:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_TAG_PATTERN:
                annotate("%s", target->identifier);
                emit_tgt(ty, target->symbol, state.fscope, def);
                break;
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                emit_expression(ty, target->object);
                emit_instr(ty, INSTR_TARGET_MEMBER);
                emit_int(ty, M_ID(target->member_name));
                break;
        case EXPRESSION_SUBSCRIPT:
                emit_expression(ty, target->container);
                emit_expression(ty, target->subscript);
                emit_instr(ty, INSTR_TARGET_SUBSCRIPT);
                break;
        default:
                fail(ty, "oh no!");
        }

        if (KEEP_LOCATION(target))
                add_location(ty, target, start, state.code.count);
}

static void
emit_dict_compr2(Ty *ty, Expr const *e)
{
        begin_loop(ty, false, true);

        offset_vector successes_save = state.match_successes;
        JumpGroup fails_save = state.match_fails;
        vec_init(state.match_successes);
        InitJumpGroup(&state.match_fails);

        emit_instr(ty, INSTR_SAVE_STACK_POS);
        emit_instr(ty, INSTR_DICT);

        emit_instr(ty, INSTR_PUSH_INDEX);
        if (e->dcompr.pattern->type == EXPRESSION_LIST) {
                emit_int(ty, (int)e->dcompr.pattern->es.count);
        } else {
                emit_int(ty, 1);
        }

        emit_expression(ty, e->dcompr.iter);

        LABEL(start);
        emit_instr(ty, INSTR_SAVE_STACK_POS);
        emit_instr(ty, INSTR_SENTINEL);
        emit_instr(ty, INSTR_CLEAR_RC);
        emit_instr(ty, INSTR_GET_NEXT);
        emit_instr(ty, INSTR_READ_INDEX);

        add_location(ty, e, start.off, state.code.count);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        emit_instr(ty, INSTR_FIX_TO);
        emit_int(ty, (int)e->dcompr.pattern->es.count);

        for (int i = 0; i < e->dcompr.pattern->es.count; ++i) {
                emit_instr(ty, INSTR_SAVE_STACK_POS);
                emit_try_match(ty, e->dcompr.pattern->es.items[i]);
                emit_instr(ty, INSTR_RESTORE_STACK_POS);
                emit_instr(ty, INSTR_POP);
        }

        JumpPlaceholder cond_fail;
        if (e->dcompr.cond != NULL) {
                emit_expression(ty, e->dcompr.cond);
                cond_fail = (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF_NOT);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, match);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        if (e->dcompr.cond != NULL)
                PATCH_JUMP(cond_fail);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        JUMP(start);

        PATCH_JUMP(match);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);

        for (int i = e->elements.count - 1; i >= 0; --i) {
                emit_expression(ty, e->keys.items[i]);
                if (e->values.items[i] != NULL)
                        emit_expression(ty, e->values.items[i]);
                else
                        emit_instr(ty, INSTR_NIL);
        }

        emit_instr(ty, INSTR_DICT_COMPR);
        emit_int(ty, (int)e->elements.count);
        JUMP(start);
        PATCH_JUMP(done);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        patch_loop_jumps(ty, start.off, state.code.count);
        emit_instr(ty, INSTR_POP);
        emit_instr(ty, INSTR_POP);

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        end_loop(ty);
}

static void
emit_array_compr2(Ty *ty, Expr const *e)
{
        begin_loop(ty, false, true);

        offset_vector successes_save = state.match_successes;
        JumpGroup fails_save = state.match_fails;
        vec_init(state.match_successes);
        InitJumpGroup(&state.match_fails);

        emit_instr(ty, INSTR_SAVE_STACK_POS);
        emit_instr(ty, INSTR_ARRAY);

        emit_instr(ty, INSTR_PUSH_INDEX);
        if (e->compr.pattern->type == EXPRESSION_LIST) {
                emit_int(ty, (int)e->compr.pattern->es.count);
        } else {
                emit_int(ty, 1);
        }

        emit_expression(ty, e->compr.iter);

        LABEL(start);
        emit_instr(ty, INSTR_SAVE_STACK_POS);
        emit_instr(ty, INSTR_SENTINEL);
        emit_instr(ty, INSTR_CLEAR_RC);
        emit_instr(ty, INSTR_GET_NEXT);
        emit_instr(ty, INSTR_READ_INDEX);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        add_location(ty, e, start.off, state.code.count);

        emit_instr(ty, INSTR_FIX_TO);
        emit_int(ty, (int)e->compr.pattern->es.count);

        for (int i = 0; i < e->compr.pattern->es.count; ++i) {
                emit_instr(ty, INSTR_SAVE_STACK_POS);
                emit_try_match(ty, e->compr.pattern->es.items[i]);
                emit_instr(ty, INSTR_RESTORE_STACK_POS);
                emit_instr(ty, INSTR_POP);
        }

        JumpPlaceholder cond_fail;
        if (e->compr.cond != NULL) {
                emit_expression(ty, e->compr.cond);
                cond_fail = (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF_NOT);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, match);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        if (e->compr.cond != NULL)
                PATCH_JUMP(cond_fail);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        JUMP(start);

        PATCH_JUMP(match);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);

        emit_instr(ty, INSTR_SAVE_STACK_POS);

        for (int i = e->elements.count - 1; i >= 0; --i) {
                if (e->aconds.items[i] != NULL) {
                        emit_expression(ty, e->aconds.items[i]);
                        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, skip);
                        emit_expression(ty, e->elements.items[i]);
                        PATCH_JUMP(skip);
                } else {
                        emit_expression(ty, e->elements.items[i]);
                }
        }

        emit_instr(ty, INSTR_ARRAY_COMPR);
        JUMP(start);
        PATCH_JUMP(done);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        patch_loop_jumps(ty, start.off, state.code.count);
        emit_instr(ty, INSTR_POP);
        emit_instr(ty, INSTR_POP);

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        end_loop(ty);
}

static void
emit_spread(Ty *ty, Expr const *e, bool nils)
{
        emit_instr(ty, INSTR_PUSH_INDEX);
        emit_int(ty, 1);

        if (e != NULL) {
                emit_expression(ty, e);
        } else {
                emit_instr(ty, INSTR_SWAP);
        }

        LABEL(start);
        emit_instr(ty, INSTR_SENTINEL);
        emit_instr(ty, INSTR_CLEAR_RC);
        emit_instr(ty, INSTR_GET_NEXT);
        emit_instr(ty, INSTR_READ_INDEX);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        emit_instr(ty, INSTR_FIX_TO);
        emit_int(ty, 1);

        emit_instr(ty, INSTR_SWAP);
        emit_instr(ty, INSTR_POP);

        emit_instr(ty, INSTR_REVERSE);
        emit_int(ty, 3);

        if (nils) {
                emit_instr(ty, INSTR_NIL);
                emit_instr(ty, INSTR_REVERSE);
                emit_int(ty, 3);
        } else {
                emit_instr(ty, INSTR_SWAP);
        }

        JUMP(start);

        PATCH_JUMP(done);

        emit_instr(ty, INSTR_FIX_TO);
        emit_int(ty, 1);

        emit_instr(ty, INSTR_POP);
        emit_instr(ty, INSTR_POP);
        emit_instr(ty, INSTR_POP);
        emit_instr(ty, INSTR_POP);
}

static void
emit_conditional(Ty *ty, Expr const *e)
{
        emit_expression(ty, e->cond);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, otherwise);
        emit_expression(ty, e->then);
        PLACEHOLDER_JUMP(INSTR_JUMP, end);
        PATCH_JUMP(otherwise);
        emit_expression(ty, e->otherwise);
        PATCH_JUMP(end);
}

static void
emit_for_each2(Ty *ty, Stmt const *s, bool want_result)
{
        begin_loop(ty, want_result, true);

        offset_vector successes_save = state.match_successes;
        JumpGroup fails_save = state.match_fails;
        vec_init(state.match_successes);
        InitJumpGroup(&state.match_fails);

        emit_instr(ty, INSTR_PUSH_INDEX);
        emit_int(ty, (int)s->each.target->es.count);

        emit_expression(ty, s->each.array);

        LABEL(start);
        emit_instr(ty, INSTR_SAVE_STACK_POS);
        emit_instr(ty, INSTR_SENTINEL);
        emit_instr(ty, INSTR_CLEAR_RC);
        emit_instr(ty, INSTR_GET_NEXT);
        emit_instr(ty, INSTR_READ_INDEX);

#ifndef TY_ENABLE_PROFILING
        add_location(ty, s->each.array, start.off, state.code.count);
#endif

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        emit_instr(ty, INSTR_FIX_TO);
        emit_int(ty, (int)s->each.target->es.count);

        if (s->each.target->has_resources) {
                emit_instr(ty, INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        for (int i = 0; i < s->each.target->es.count; ++i) {
                emit_instr(ty, INSTR_SAVE_STACK_POS);
                emit_try_match(ty, s->each.target->es.items[i]);
                emit_instr(ty, INSTR_RESTORE_STACK_POS);
                emit_instr(ty, INSTR_POP);
        }

        JumpPlaceholder should_stop;
        if (s->each.stop != NULL) {
                emit_expression(ty, s->each.stop);
                should_stop = (PLACEHOLDER_JUMP)(ty, INSTR_JUMP_IF_NOT);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, match);

        EMIT_GROUP_LABEL(state.match_fails, ":Fail");
        patch_jumps_to(&state.match_fails, state.code.count);

        // FIXME: are these useless?
        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        emit_instr(ty, INSTR_RESTORE_STACK_POS);

        // Element doesn't match the for loop pattern
        add_location(ty, s->each.target, state.code.count, state.code.count + 1);
        emit_instr(ty, INSTR_BAD_MATCH);

        PATCH_JUMP(match);

        emit_instr(ty, INSTR_RESTORE_STACK_POS);

        if (s->each.cond != NULL) {
                emit_expression(ty, s->each.cond);
                JUMP_IF_NOT(start);
        }

        emit_statement(ty, s->each.body, false);

        if (s->each.target->has_resources) {
                emit_instr(ty, INSTR_DROP);
                state.resources -= 1;
        }

        JUMP(start);

        if (s->each.stop != NULL)
                PATCH_JUMP(should_stop);

        PATCH_JUMP(done);

        emit_instr(ty, INSTR_RESTORE_STACK_POS);
        emit_instr(ty, INSTR_POP);
        emit_instr(ty, INSTR_POP);

        if (want_result)
                emit_instr(ty, INSTR_NIL);

        patch_loop_jumps(ty, start.off, state.code.count);

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        end_loop(ty);
}

static bool
check_multi(Expr *target, Expr const *e, int *n)
{
        if (is_call(e))
                return true;

        if (e->type != EXPRESSION_LIST)
                return (*n = 1), false;

        for (*n = 0; *n < e->es.count; ++*n) {
                if (is_call(e->es.items[*n]) || e->es.items[*n]->type == EXPRESSION_SPREAD)
                        return true;
        }

        return *n == target->es.count;
}

static void
emit_assignment2(Ty *ty, Expr *target, bool maybe, bool def)
{
        char instr = maybe ? INSTR_MAYBE_ASSIGN : INSTR_ASSIGN;

        size_t start = state.code.count;

        bool after = false;

        switch (target->type) {
        case EXPRESSION_ARRAY:
                for (int i = 0; i < target->elements.count; ++i) {
                        if (target->elements.items[i]->type == EXPRESSION_MATCH_REST) {
                                if (after) {
                                        PushContext(ty, target->elements.items[i]);
                                        fail(ty, "array pattern cannot contain multiple gather elements");
                                } else {
                                        after = true;
                                }
                                emit_target(ty, target->elements.items[i], def);
                                emit_instr(ty, INSTR_ARRAY_REST);
                                emit_int(ty, i);
                                emit_int(ty, target->elements.count - i - 1);
                                emit_int(ty, sizeof (int) + 1);
                                emit_instr(ty, INSTR_JUMP);
                                emit_int(ty, 1);
                                emit_instr(ty, INSTR_BAD_MATCH);
                        } else {
                                emit_instr(ty, INSTR_PUSH_ARRAY_ELEM);
                                if (after) {
                                        if (target->optional.items[i]) {
                                                PushContext(ty, target->elements.items[i]);
                                                fail(ty, "optional element cannot come after a gather element in array pattern");
                                        }
                                        emit_int(ty, i - target->elements.count);
                                } else {
                                        emit_int(ty, i);
                                }
                                emit_boolean(ty, !target->optional.items[i]);
                                emit_assignment2(ty, target->elements.items[i], maybe, def);
                                emit_instr(ty, INSTR_POP);
                        }
                }
                break;
        case EXPRESSION_DICT:
                for (int i = 0; i < target->keys.count; ++i) {
                        emit_instr(ty, INSTR_DUP);
                        emit_expression(ty, target->keys.items[i]);
                        emit_instr(ty, INSTR_SUBSCRIPT);
                        emit_assignment2(ty, target->values.items[i], maybe, def);
                        emit_instr(ty, INSTR_POP);
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_instr(ty, INSTR_UNTAG_OR_DIE);
                emit_int(ty, tag_app_tag(target));
                emit_assignment2(ty, target->tagged, maybe, def);
                break;
        case EXPRESSION_TAG_PATTERN:
                emit_target(ty, target, def);
                emit_instr(ty, INSTR_STEAL_TAG);
                emit_assignment2(ty, target->tagged, maybe, def);
                break;
        case EXPRESSION_VIEW_PATTERN:
                emit_instr(ty, INSTR_DUP);
                emit_expression(ty, target->left);
                emit_instr(ty, INSTR_CALL);
                emit_int(ty, 1);
                emit_int(ty, 0);
                add_location(ty, target->left, start, state.code.count);
                emit_assignment2(ty, target->right, maybe, def);
                emit_instr(ty, INSTR_POP);
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                emit_instr(ty, INSTR_DUP);
                emit_expression(ty, target->left);
                emit_instr(ty, INSTR_CALL);
                emit_int(ty, 1);
                emit_int(ty, 0);
                add_location(ty, target->left, start, state.code.count);
                emit_instr(ty, INSTR_THROW_IF_NIL);
                add_location(ty, target, state.code.count - 1, state.code.count);
                emit_assignment2(ty, target->right, maybe, def);
                emit_instr(ty, INSTR_POP);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_instr(ty, INSTR_THROW_IF_NIL);
                emit_target(ty, target, def);
                emit_instr(ty, instr);
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < target->es.count; ++i) {
                        if (target->es.items[i]->type == EXPRESSION_MATCH_REST) {
                                if (has_any_names(target)) {
                                        emit_record_rest(ty, target, i, true);
                                } else {
                                        // FIXME: should we handle elements after the match-rest?
                                        emit_target(ty, target->es.items[i], def);
                                        emit_instr(ty, INSTR_TUPLE_REST);
                                        emit_int(ty, i);
                                        emit_int(ty, sizeof (int) + 1);
                                        emit_instr(ty, INSTR_JUMP);
                                        emit_int(ty, 1);
                                        emit_instr(ty, INSTR_BAD_MATCH);
                                }
                        } else if (target->names.items[i] != NULL) {
                                emit_instr(ty, INSTR_PUSH_TUPLE_MEMBER);
                                emit_boolean(ty, target->required.items[i]);
                                emit_int(ty, M_ID(target->names.items[i]));
                                emit_assignment2(ty, target->es.items[i], maybe, def);
                                emit_instr(ty, INSTR_POP);
                        } else {
                                emit_instr(ty, INSTR_PUSH_TUPLE_ELEM);
                                emit_int(ty, i);
                                emit_assignment2(ty, target->es.items[i], maybe, def);
                                emit_instr(ty, INSTR_POP);
                        }
                }
                break;
        default:
                emit_target(ty, target, def);
                emit_instr(ty, instr);
                if (target->type == EXPRESSION_IDENTIFIER && target->constraint != NULL && CheckConstraints) {
                        size_t start = state.code.count;
                        emit_instr(ty, INSTR_DUP);
                        emit_expression(ty, target->constraint);
                        emit_instr(ty, INSTR_CHECK_MATCH);
                        PLACEHOLDER_JUMP(INSTR_JUMP_IF, good);
                        emit_instr(ty, INSTR_BAD_ASSIGN);
                        emit_string(ty, target->identifier);
                        PATCH_JUMP(good);
                        add_location(ty, target->constraint, start, state.code.count);
                }

#ifndef TY_ENABLE_PROFILING
                // Don't need location info, can't fail here
                return;
#endif
        }

        add_location(ty, target, start, state.code.count);
}

static void
emit_assignment(Ty *ty, Expr *target, Expr const *e, bool maybe, bool def)
{
        if (target->has_resources) {
                emit_instr(ty, INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        if (target->type == EXPRESSION_LIST) {
                emit_list(ty, e);
                emit_instr(ty, INSTR_FIX_TO);
                emit_int(ty, target->es.count);
                for (int i = 0; i < target->es.count; ++i) {
                        emit_assignment2(ty, target->es.items[i], maybe, def);
                        emit_instr(ty, INSTR_POP);
                }
                emit_instr(ty, INSTR_POP);
                emit_instr(ty, INSTR_NIL);
        } else {
                emit_expression(ty, e);
                emit_assignment2(ty, target, maybe, def);
        }
}

static void
emit_non_nil_expr(Ty *ty, Expr const *e, bool none)
{
        emit_expression(ty, e);
        emit_instr(ty, INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NIL, skip);
        PLACEHOLDER_JUMP(INSTR_JUMP, good);
        PATCH_JUMP(skip);

        emit_instr(ty, INSTR_POP);

        if (none) {
                emit_instr(ty, INSTR_NONE);
        }

        PATCH_JUMP(good);
}

static void
emit_expr(Ty *ty, Expr const *e, bool need_loc)
{
        state.start = e->start;
        state.end = e->end;

        size_t start = state.code.count;
        char const *method = NULL;

        TryState *try = get_try(ty, 0);

        void *ctx = PushContext(ty, e);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                // FIXME
                if (false) {
                        fail(ty, "%s%s%s is uninitialized here", TERM(93), e->identifier, TERM(0));
                }
                emit_load(ty, e->symbol, state.fscope);
                break;
        case EXPRESSION_IFDEF:
                emit_load(ty, e->symbol, state.fscope);
                emit_instr(ty, INSTR_TAG_PUSH);
                emit_int(ty, TAG_SOME);
                break;
        case EXPRESSION_NONE:
                emit_instr(ty, INSTR_TAG);
                emit_int(ty, TAG_NONE);
                break;
        case EXPRESSION_VALUE:
                emit_instr(ty, INSTR_VALUE);
                emit_symbol(ty, (uintptr_t)e->v);
                break;
        case EXPRESSION_MATCH:
                emit_match_expression(ty, e);
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_expression(ty, e->tagged);
                emit_instr(ty, INSTR_TAG_PUSH);
                emit_int(ty, tag_app_tag(e));
                break;
        case EXPRESSION_DOT_DOT:
                emit_expression(ty, e->left);
                if (e->right != NULL) {
                        emit_expression(ty, e->right);
                        emit_instr(ty, INSTR_RANGE);
                } else {
                        method = "__count__";
                        emit_instr(ty, INSTR_CALL_METHOD);
                        emit_int(ty, 0);
                        emit_int(ty, M_ID(method));
                        emit_int(ty, 0);
                }
                break;
        case EXPRESSION_DOT_DOT_DOT:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_INCRANGE);
                break;
        case EXPRESSION_EQ:
                emit_assignment(ty, e->target, e->value, false, false);
                break;
        case EXPRESSION_MAYBE_EQ:
                emit_assignment(ty, e->target, e->value, true, false);
                break;
        case EXPRESSION_INTEGER:
                if (e->integer == 0xCAFEBABE) {
                        emit_instr(ty, INSTR_TRAP);
                } else {
                        emit_instr(ty, INSTR_INTEGER);
                        emit_integer(ty, e->integer);
                }
                break;
        case EXPRESSION_BOOLEAN:
                emit_instr(ty, INSTR_BOOLEAN);
                emit_boolean(ty, e->boolean);
                break;
        case EXPRESSION_REAL:
                emit_instr(ty, INSTR_REAL);
                emit_float(ty, e->real);
                break;
        case EXPRESSION_STRING:
                emit_instr(ty, INSTR_STRING);
                emit_string(ty, e->string);
                break;
        case EXPRESSION_SPECIAL_STRING:
                emit_special_string(ty, e);
                break;
        case EXPRESSION_EVAL:
                emit_expression(ty, e->operand);
                emit_instr(ty, INSTR_EVAL);
                emit_symbol(ty, (uintptr_t)e->escope);
                break;
        case EXPRESSION_TAG:
                emit_instr(ty, INSTR_TAG);
                emit_int(ty, e->symbol->tag);
                break;
        case EXPRESSION_REGEX:
                emit_instr(ty, INSTR_REGEX);
                emit_symbol(ty, (uintptr_t)e->regex);
                break;
        case EXPRESSION_ARRAY:
                emit_instr(ty, INSTR_SAVE_STACK_POS);
                for (int i = 0; i < e->elements.count; ++i) {
                        if (e->aconds.items[i] != NULL) {
                                emit_expression(ty, e->aconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, skip);
                                if (e->optional.items[i]) {
                                        emit_non_nil_expr(ty, e->elements.items[i], false);
                                } else {
                                        emit_expression(ty, e->elements.items[i]);
                                }
                                PATCH_JUMP(skip);
                        } else if (e->optional.items[i]) {
                                emit_non_nil_expr(ty, e->elements.items[i], false);
                        } else {
                                emit_expression(ty, e->elements.items[i]);
                        }
                }
                emit_instr(ty, INSTR_ARRAY);
                break;
        case EXPRESSION_ARRAY_COMPR:
                emit_array_compr2(ty, e);
                break;
        case EXPRESSION_DICT:
                emit_instr(ty, INSTR_SAVE_STACK_POS);
                for (int i = e->keys.count - 1; i >= 0; --i) {
                        if (e->keys.items[i]->type == EXPRESSION_SPREAD) {
                                emit_spread(ty, e->keys.items[i]->value, true);
                        } else {
                                emit_expression(ty, e->keys.items[i]);
                                if (e->keys.items[i]->type == EXPRESSION_SPLAT) {
                                        emit_instr(ty, INSTR_NONE);
                                } else if (e->values.items[i] == NULL) {
                                        emit_instr(ty, INSTR_NIL);
                                } else {
                                        emit_expression(ty, e->values.items[i]);
                                }
                        }
                }
                emit_instr(ty, INSTR_DICT);
                if (e->dflt != NULL) {
                        emit_expression(ty, e->dflt);
                        emit_instr(ty, INSTR_DICT_DEFAULT);
                }
                break;
        case EXPRESSION_DICT_COMPR:
                emit_dict_compr2(ty, e);
                break;
        case EXPRESSION_NIL:
                emit_instr(ty, INSTR_NIL);
                break;
        case EXPRESSION_SELF:
                emit_instr(ty, INSTR_NIL);
                break;
        case EXPRESSION_SPLAT:
                emit_expression(ty, e->value);
                break;
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                emit_expression(ty, e->object);
                if (e->maybe)
                        emit_instr(ty, INSTR_TRY_MEMBER_ACCESS);
                else
                        emit_instr(ty, INSTR_MEMBER_ACCESS);
                emit_int(ty, M_ID(e->member_name));
                break;
        case EXPRESSION_SUBSCRIPT:
                emit_expression(ty, e->container);
                emit_expression(ty, e->subscript);
                emit_instr(ty, INSTR_SUBSCRIPT);
                break;
        case EXPRESSION_SLICE:
                if (e->slice.i != NULL) emit_expression(ty, e->slice.i);
                else                    emit_instr(ty, INSTR_NIL);
                if (e->slice.j != NULL) emit_expression(ty, e->slice.j);
                else                    emit_instr(ty, INSTR_NIL);
                if (e->slice.k != NULL) emit_expression(ty, e->slice.k);
                else                    emit_instr(ty, INSTR_NIL);
                emit_expression(ty, e->slice.e);
                emit_instr(ty, INSTR_SLICE);
                break;
        case EXPRESSION_STATEMENT:
                emit_statement(ty, e->statement, true);
                break;
        case EXPRESSION_FUNCTION_CALL:
                if (is_variadic(e)) {
                        emit_instr(ty, INSTR_SAVE_STACK_POS);
                }

                for (size_t i = 0; i < e->args.count; ++i) {
                        if (e->args.items[i] == NULL) {
                                continue;
                        } else if (e->fconds.items[i] != NULL) {
                                emit_expression(ty, e->fconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, skip);
                                emit_expression(ty, e->args.items[i]);
                                PATCH_JUMP(skip);
                        } else {
                                emit_expression(ty, e->args.items[i]);
                        }
                }

                for (size_t i = 0; i < e->kwargs.count; ++i) {
                        if (e->fkwconds.items[i] == NULL) {
                                emit_expression(ty, e->kwargs.items[i]);
                        } else {
                                emit_expression(ty, e->fkwconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_NONE_IF_NOT, skip);

                                emit_expression(ty, e->kwargs.items[i]);
                                PATCH_JUMP(skip);
                        }
                }

                emit_expression(ty, e->function);
                emit_instr(ty, INSTR_CALL);

                if (is_variadic(e)) {
                        emit_int(ty, -1);
                } else {
                        emit_int(ty, e->args.count);
                }

                emit_int(ty, e->kwargs.count);
                for (size_t i = e->kws.count; i > 0; --i) {
                        emit_string(ty, e->kws.items[i - 1]);
                }

                break;
        case EXPRESSION_METHOD_CALL:
                if (is_variadic(e)) {
                        emit_instr(ty, INSTR_SAVE_STACK_POS);
                }
                for (size_t i = 0; i < e->method_args.count; ++i) {
                        if (e->method_args.items[i] == NULL) {
                                continue;
                        } else if (e->mconds.items[i] != NULL) {
                                emit_expression(ty, e->mconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, skip);
                                emit_expression(ty, e->method_args.items[i]);
                                PATCH_JUMP(skip);
                        } else {
                                emit_expression(ty, e->method_args.items[i]);
                        }
                }
                for (size_t i = 0; i < e->method_kwargs.count; ++i) {
                        emit_expression(ty, e->method_kwargs.items[i]);
                }
                emit_expression(ty, e->object);
                if (e->maybe)
                        emit_instr(ty, INSTR_TRY_CALL_METHOD);
                else
                        emit_instr(ty, INSTR_CALL_METHOD);
                if (is_variadic(e)) {
                        emit_int(ty, -1);
                } else {
                        emit_int(ty, e->method_args.count);
                }

                emit_int(ty, (int)intern(&xD.members, e->method_name)->id);

                emit_int(ty, e->method_kwargs.count);
                for (size_t i = e->method_kws.count; i > 0; --i) {
                        emit_string(ty, e->method_kws.items[i - 1]);
                }
                break;
        case EXPRESSION_WITH:
                emit_with(ty, e);
                break;
        case EXPRESSION_YIELD:
                emit_yield(ty, (Expr const **)e->es.items, e->es.count, true);
                break;
        case EXPRESSION_THROW:
                if (try != NULL && try->finally) {
                        fail(ty, "invalid 'throw' statement (occurs in a finally block)");
                }
                emit_expression(ty, e->throw);
                emit_instr(ty, INSTR_THROW);
                break;
        case EXPRESSION_SPREAD:
                emit_spread(ty, e->value, false);
                break;
        case EXPRESSION_USER_OP:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_BINARY_OP);
                emit_int(ty, intern(&xD.b_ops, e->op_name)->id);
                break;
        case EXPRESSION_BIT_OR:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_BINARY_OP);
                emit_int(ty, OP_BIT_OR);
                break;
        case EXPRESSION_BIT_AND:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_BINARY_OP);
                emit_int(ty, OP_BIT_AND);
                break;
        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
                method = "contains?";
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_CALL_METHOD);
                emit_int(ty, 1);
                emit_int(ty, M_ID(method));
                emit_int(ty, 0);
                if (e->type == EXPRESSION_NOT_IN) {
                        emit_instr(ty, INSTR_NOT);
                }
                break;
        case EXPRESSION_GENERATOR:
                emit_function(ty, e, -1);
                emit_instr(ty, INSTR_CALL);
                emit_int(ty, 0);
                emit_int(ty, 0);
                break;
        case EXPRESSION_FUNCTION:
        case EXPRESSION_MULTI_FUNCTION:
                emit_function(ty, e, -1);
                break;
        case EXPRESSION_PLUS:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_ADD);
                break;
        case EXPRESSION_MINUS:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_SUB);
                break;
        case EXPRESSION_STAR:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_MUL);
                break;
        case EXPRESSION_DIV:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_DIV);
                break;
        case EXPRESSION_PERCENT:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_MOD);
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
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_LT);
                break;
        case EXPRESSION_LEQ:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_LEQ);
                break;
        case EXPRESSION_GT:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_GT);
                break;
        case EXPRESSION_GEQ:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_GEQ);
                break;
        case EXPRESSION_CMP:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_CMP);
                break;
        case EXPRESSION_DBL_EQ:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_EQ);
                break;
        case EXPRESSION_NOT_EQ:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_NEQ);
                break;
        case EXPRESSION_CHECK_MATCH:
                emit_expression(ty, e->left);
                emit_expression(ty, e->right);
                emit_instr(ty, INSTR_CHECK_MATCH);
                break;
        case EXPRESSION_PREFIX_BANG:
                emit_expression(ty, e->operand);
                emit_instr(ty, INSTR_NOT);
                break;
        case EXPRESSION_PREFIX_HASH:
                emit_expression(ty, e->operand);
                emit_instr(ty, INSTR_COUNT);
                break;
        case EXPRESSION_PREFIX_QUESTION:
                emit_expression(ty, e->operand);
                emit_instr(ty, INSTR_QUESTION);
                break;
        case EXPRESSION_PREFIX_AT:
                emit_expression(ty, e->operand);
                emit_instr(ty, INSTR_GET_TAG);
                break;
        case EXPRESSION_PREFIX_MINUS:
                emit_expression(ty, e->operand);
                emit_instr(ty, INSTR_NEG);
                break;
        case EXPRESSION_PREFIX_INC:
                emit_target(ty, e->operand, false);
                emit_instr(ty, INSTR_PRE_INC);
                break;
        case EXPRESSION_PREFIX_DEC:
                emit_target(ty, e->operand, false);
                emit_instr(ty, INSTR_PRE_DEC);
                break;
        case EXPRESSION_POSTFIX_INC:
                emit_target(ty, e->operand, false);
                emit_instr(ty, INSTR_POST_INC);
                break;
        case EXPRESSION_POSTFIX_DEC:
                emit_target(ty, e->operand, false);
                emit_instr(ty, INSTR_POST_DEC);
                break;
        case EXPRESSION_PLUS_EQ:
                emit_expression(ty, e->value);
                emit_target(ty, e->target, false);
                emit_instr(ty, INSTR_MUT_ADD);
                break;
        case EXPRESSION_STAR_EQ:
                emit_target(ty, e->target, false);
                emit_expression(ty, e->value);
                emit_instr(ty, INSTR_MUT_MUL);
                break;
        case EXPRESSION_DIV_EQ:
                emit_target(ty, e->target, false);
                emit_expression(ty, e->value);
                emit_instr(ty, INSTR_MUT_DIV);
                break;
        case EXPRESSION_MINUS_EQ:
                emit_target(ty, e->target, false);
                emit_expression(ty, e->value);
                emit_instr(ty, INSTR_MUT_SUB);
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        if (e->tconds.items[i] != NULL) {
                                emit_expression(ty, e->tconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, skip);
                                if (!e->required.items[i]) {
                                        emit_non_nil_expr(ty, e->es.items[i], true);
                                } else {
                                        emit_expression(ty, e->es.items[i]);
                                }
                                PLACEHOLDER_JUMP(INSTR_JUMP, good);
                                PATCH_JUMP(skip);
                                emit_instr(ty, INSTR_NONE);
                                PATCH_JUMP(good);
                        } else if (!e->required.items[i]) {
                                emit_non_nil_expr(ty, e->es.items[i], true);
                        } else if (e->es.items[i]->type == EXPRESSION_SPREAD) {
                                emit_expression(ty, e->es.items[i]->value);
                        } else {
                                emit_expression(ty, e->es.items[i]);
                        }
                }
                emit_instr(ty, INSTR_TUPLE);
                emit_int(ty, e->es.count);
                for (int i = 0; i < e->names.count; ++i) {
                        if (e->names.items[i] != NULL) {
                                if (strcmp(e->names.items[i], "*") == 0) {
                                        emit_int(ty, -2);
                                } else {
                                        emit_int(ty, (int)intern(&xD.members, e->names.items[i])->id);
                                }
                        } else {
                                emit_int(ty, -1);
                        }
                }
                break;
        case EXPRESSION_TEMPLATE:
                for (int i = e->template.exprs.count - 1; i >= 0; --i) {
                        emit_expression(ty, e->template.exprs.items[i]);
                }
                emit_instr(ty, INSTR_RENDER_TEMPLATE);
                emit_symbol(ty, (uintptr_t)e);
                break;
        default:
                fail(ty, "expression unexpected in this context: %s", ExpressionTypeName(e));
        }

        if (KEEP_LOCATION(e) || need_loc)
                add_location(ty, e, start, state.code.count);

        RestoreContext(ty, ctx);
}

static void
emit_expression(Ty *ty, Expr const *e)
{
        emit_expr(ty, e, false);
}

static bool
emit_statement(Ty *ty, Stmt const *s, bool want_result)
{
        state.start = s->start;
        state.end = s->end;

        bool returns = false;

        int resources = state.resources;

#ifdef TY_ENABLE_PROFILING
        size_t start = state.code.count;
#endif

        LoopState *loop = get_loop(ty, 0);

        void *ctx = PushContext(ty, s);

        switch (s->type) {
        case STATEMENT_BLOCK:
        case STATEMENT_MULTI:
                for (int i = 0; !returns && i < s->statements.count; ++i) {
                        bool wr = want_result && (i + 1 == s->statements.count);
                        returns |= emit_statement(ty, s->statements.items[i], wr);
                }
                if (s->statements.count > 0) {
                        want_result = false;
                }
                while (state.resources > resources) {
                        emit_instr(ty, INSTR_DROP);
                        state.resources -= 1;
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
                emit_for_each2(ty, s, want_result);
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
                emit_expression(ty, s->expression);
                if (!want_result) {
                        emit_instr(ty, INSTR_POP);
                } else {
                        want_result = false;
                }
                break;
        case STATEMENT_OPERATOR_DEFINITION:
        case STATEMENT_DEFINITION:
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
                emit_assignment(ty, s->target, s->value, false, true);
                emit_instr(ty, INSTR_POP);
                break;
        case STATEMENT_TAG_DEFINITION:
                for (int i = 0; i < s->tag.statics.count; ++i) {
                        emit_function(ty, s->tag.statics.items[i], CLASS_TAG);
                }

                for (int i = 0; i < s->tag.methods.count; ++i) {
                        emit_function(ty, s->tag.methods.items[i], CLASS_TAG);
                }

                emit_instr(ty, INSTR_DEFINE_TAG);
                emit_int(ty, s->tag.symbol);
                emit_int(ty, s->tag.super == NULL ? -1 : s->tag.super->symbol->tag);
                emit_int(ty, s->tag.methods.count);
                emit_int(ty, s->tag.statics.count);

                for (int i = s->tag.methods.count; i > 0; --i) {
                        emit_string(ty, s->tag.methods.items[i - 1]->name);
                }

                for (int i = s->tag.statics.count; i > 0; --i) {
                        emit_string(ty, s->tag.statics.items[i - 1]->name);
                }

                break;
        case STATEMENT_CLASS_DEFINITION:
                for (int i = 0; i < s->class.setters.count; ++i) {
                        state.method = s->class.setters.items[i]->scope;
                        s->class.setters.items[i]->mtype = MT_SET;
                        emit_function(ty, s->class.setters.items[i], s->class.symbol);
                }
                for (int i = 0; i < s->class.getters.count; ++i) {
                        state.method = s->class.getters.items[i]->scope;
                        s->class.getters.items[i]->mtype = MT_GET;
                        emit_function(ty, s->class.getters.items[i], s->class.symbol);
                }
                for (int i = 0; i < s->class.methods.count; ++i) {
                        state.method = s->class.methods.items[i]->scope;
                        s->class.methods.items[i]->mtype = MT_INSTANCE;
                        emit_function(ty, s->class.methods.items[i], s->class.symbol);
                }
                for (int i = 0; i < s->class.statics.count; ++i) {
                        state.method = s->class.statics.items[i]->scope;
                        s->class.statics.items[i]->mtype = MT_STATIC;
                        emit_function(ty, s->class.statics.items[i], s->class.symbol);
                }

                emit_instr(ty, INSTR_DEFINE_CLASS);
                emit_int(ty, s->class.symbol);
                emit_int(ty, s->class.statics.count);
                emit_int(ty, s->class.methods.count);
                emit_int(ty, s->class.getters.count);
                emit_int(ty, s->class.setters.count);

                for (int i = s->class.statics.count; i > 0; --i)
                        emit_string(ty, s->class.statics.items[i - 1]->name);

                for (int i = s->class.methods.count; i > 0; --i)
                        emit_string(ty, s->class.methods.items[i - 1]->name);

                for (int i = s->class.getters.count; i > 0; --i)
                        emit_string(ty, s->class.getters.items[i - 1]->name);

                for (int i = s->class.setters.count; i > 0; --i)
                        emit_string(ty, s->class.setters.items[i - 1]->name);

                break;
        case STATEMENT_CLEANUP:
                want_result = false;
                emit_instr(ty, INSTR_CLEANUP);
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
                emit_yield(ty, (Expr const **)s->returns.items, s->returns.count, false);
                emit_instr(ty, INSTR_JUMP);
                avP(state.generator_returns, state.code.count);
                emit_int(ty, 0);
                break;
        case STATEMENT_BREAK:
                loop = get_loop(ty, s->depth - 1);

                if (loop == NULL) {
                        fail(ty, "invalid break statement (not inside a loop)");
                }

                for (int i = 0; i < s->depth; ++i) {
                        if (get_loop(ty, i)->each) {
                                emit_instr(ty, INSTR_POP);
                                emit_instr(ty, INSTR_POP);
                        }
                }

                want_result = false;

                if (s->expression != NULL) {
                        emit_expression(ty, s->expression);
                        if (!loop->wr)
                                emit_instr(ty, INSTR_POP);
                } else if (loop->wr) {
                        emit_instr(ty, INSTR_NIL);
                }

                for (int i = 0; get_try(ty, i) != NULL && get_try(ty, i)->t > loop->t; ++i) {
                        emit_instr(ty, INSTR_FINALLY);
                }

                for (int i = loop->resources; i < state.resources; ++i) {
                        emit_instr(ty, INSTR_DROP);
                }

                emit_instr(ty, INSTR_JUMP);
                avP(loop->breaks, state.code.count);
                emit_int(ty, 0);
                break;
        case STATEMENT_CONTINUE:
                loop = get_loop(ty, s->depth - 1);

                if (loop == NULL)
                        fail(ty, "invalid continue statement (not inside a loop)");

                for (int i = 0; i < s->depth - 1; ++i) {
                        if (get_loop(ty, i)->each) {
                                emit_instr(ty, INSTR_POP);
                                emit_instr(ty, INSTR_POP);
                        }
                }

                for (int i = 0; get_try(ty, i) != NULL && get_try(ty, i)->t > loop->t; ++i) {
                        emit_instr(ty, INSTR_FINALLY);
                }

                for (int i = loop->resources; i < state.resources; ++i) {
                        emit_instr(ty, INSTR_DROP);
                }

                emit_instr(ty, INSTR_JUMP);
                avP(loop->continues, state.code.count);
                emit_int(ty, 0);
                break;
        case STATEMENT_DROP:
                for (int i = 0; i < s->drop.count; ++i) {
                        emit_load(ty, s->drop.items[i], state.fscope);
                        emit_instr(ty, INSTR_TRY_CALL_METHOD);
                        emit_int(ty, 0);
                        emit_int(ty, (int)intern(&xD.members, "__drop__")->id);
                        emit_int(ty, 0);
                        emit_instr(ty, INSTR_POP);
                }
                break;
        case STATEMENT_DEFER:
                emit_expression(ty, s->expression);
                emit_instr(ty, INSTR_DEFER);
                break;
        case STATEMENT_NEXT:
                emit_expression(ty, s->expression);
                emit_instr(ty, INSTR_NEXT);
                break;
        }

        if (want_result)
                emit_instr(ty, INSTR_NIL);

        RestoreContext(ty, ctx);

#ifdef TY_ENABLE_PROFILING
        if (
                s->type != STATEMENT_BLOCK &&
                s->type != STATEMENT_MULTI &&
                (s->type != STATEMENT_EXPRESSION || !want_result)
        ) {
                Expr *e = NewExpr(ty, EXPRESSION_STATEMENT);
                e->start = s->start;
                e->end = s->end;
                e->filename = state.filename;
                e->statement = s;
                add_location(ty, e, start, state.code.count);
        }
#endif

        return returns;
}

static void
emit_new_globals(Ty *ty)
{
        for (size_t i = GlobalCount; i < global->owned.count; ++i) {
                Symbol *s = global->owned.items[i];
                if (s->i < BuiltinCount)
                        continue;
                if (s->tag != -1) {
                        emit_instr(ty, INSTR_TAG);
                        emit_int(ty, s->tag);
                        annotate("%s", s->identifier);
                        emit_instr(ty, INSTR_TARGET_GLOBAL);
                        emit_int(ty, s->i);
                        emit_instr(ty, INSTR_ASSIGN);
                        emit_instr(ty, INSTR_POP);
                } else if (s->class >= 0) {
                        emit_instr(ty, INSTR_CLASS);
                        emit_int(ty, s->class);
                        annotate("%s", s->identifier);
                        emit_instr(ty, INSTR_TARGET_GLOBAL);
                        emit_int(ty, s->i);
                        emit_instr(ty, INSTR_ASSIGN);
                        emit_instr(ty, INSTR_POP);
                }
        }

        GlobalCount = global->owned.count;
}

static import_vector
get_module_public_imports(char const *name)
{
        for (int i = 0; i < modules.count; ++i)
                if (strcmp(name, modules.items[i].path) == 0)
                        return modules.items[i].imports;

        return (import_vector){0};
}

static Scope *
get_module_scope(char const *name)
{
        for (int i = 0; i < modules.count; ++i)
                if (strcmp(name, modules.items[i].path) == 0)
                        return modules.items[i].scope;

        return NULL;
}

static void
declare_classes(Ty *ty, Stmt *s, Scope *scope)
{
        Scope *ns = (scope != NULL) ? scope : GetNamespace(ty, s->ns);

        if (s->type == STATEMENT_MULTI) {
                for (int i = 0; i < s->statements.count; ++i) {
                        declare_classes(ty, s->statements.items[i], ns);
                }
        } else if (s->type == STATEMENT_CLASS_DEFINITION) {
                if (scope_locally_defined(ty, ns, s->class.name)) {
                        fail(
                                ty,
                                "redeclaration of class %s%s%s%s%s",
                                TERM(1),
                                TERM(34),
                                s->class.name,
                                TERM(22),
                                TERM(39)
                        );
                }
                Symbol *sym = addsymbol(ty, ns, s->class.name);
                sym->class = class_new(ty, s->class.name, s->class.doc);
                sym->cnst = true;
                s->class.symbol = sym->class;
        }
}

inline static bool
is_proc_def(Stmt const *s)
{
        return s->type == STATEMENT_FUNCTION_DEFINITION ||
               s->type == STATEMENT_OPERATOR_DEFINITION;
}

static void
compile(Ty *ty, char const *source)
{
        Stmt **p = parse(ty, source, state.filename);
        if (p == NULL) {
                Error = parse_error(ty);
                longjmp(jb, 1);
        }

        statement_vector multi_functions = {0};

        for (size_t i = 0; p[i] != NULL; ++i) {
                if (
                        p[i + 1] != NULL &&
                        p[i    ]->type == STATEMENT_FUNCTION_DEFINITION &&
                        p[i + 1]->type == STATEMENT_FUNCTION_DEFINITION &&
                        strcmp(p[i]->target->identifier, p[i + 1]->target->identifier) == 0
                ) {
                        char buffer[1024];
                        Expr *multi = mkmulti(ty, p[i]->target->identifier, false);
                        bool pub = p[i]->pub;

                        Stmt *def = NewStmt(ty, STATEMENT_FUNCTION_DEFINITION);

                        def->value = multi;
                        def->pub = pub;

                        def->target = NewExpr(ty, EXPRESSION_IDENTIFIER);
                        def->target->start      = p[i]->target->start;
                        def->target->end        = p[i]->target->end;
                        def->target->filename   = state.filename;
                        def->target->identifier = multi->name;

                        define_function(ty, def);
                        symbolize_statement(ty, state.global, def);

                        int m = 0;
                        do {
                                p[i + m]->pub = false;
                                p[i + m]->value->is_overload = true;
                                snprintf(buffer, sizeof buffer, "%s#%d", multi->name, m + 1);
                                p[i + m]->target->identifier = p[i + m]->value->name = sclonea(ty, buffer);
                                avP(multi->functions, (Expr *)p[i + m]);
                                define_function(ty, p[i + m]);
                                symbolize_statement(ty, state.global, p[i + m]);
                                m += 1;
                        } while (
                                p[i + m] != NULL &&
                                p[i + m]->type == STATEMENT_FUNCTION_DEFINITION &&
                                strcmp(multi->name, p[i + m]->target->identifier) == 0
                        );

                        avP(multi_functions, def);
                }
        }

        for (size_t i = 0; p[i] != NULL; ++i) {
                symbolize_statement(ty, state.global, p[i]);
        }

        for (int i = 0; i < state.class_ops.count; ++i) {
                symbolize_statement(ty, state.global, state.class_ops.items[i]);
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
                        for (
                                int j = i - 1;

                                (j >= 0) && !is_proc_def(p[j]) && p[j]->type != STATEMENT_IMPORT;

                                j -= 1
                        ) {
                                Stmt *s = p[j];
                                p[j] = p[j + 1];
                                p[end_of_defs = j + 1] = s;
                        }
                }
        }

        for (int i = 0; i < multi_functions.count; ++i) {
                emit_statement(ty, multi_functions.items[i], false);
        }

        for (int i = 0; i < end_of_defs; ++i) {
                emit_statement(ty, p[i], false);
        }

        for (int i = 0; i < state.class_ops.count; ++i) {
                emit_statement(ty, state.class_ops.items[i], false);
        }

        for (int i = end_of_defs; p[i] != NULL; ++i) {
                emit_statement(ty, p[i], false);
        }

        while (state.resources > 0) {
                emit_instr(ty, INSTR_DROP);
                state.resources -= 1;
        }

        emit_instr(ty, INSTR_HALT);

        /*
         * We can re-use this vec(Stmt *) for further compilation but it's important
         * that we empty it here. Because we stripped the constraints out of the
         * functions, passing them to symbolize_op_def() again will provide new
         * implementations of the operators that match /any/ operands.
         */
        state.class_ops.count = 0;

        /*
         * Add all of the location information from this compliation unit to the global list.
         */
        add_location_info(ty);

        state.generator_returns.count = 0;
        state.tries.count = 0;
        state.loops.count = 0;

        add_annotation(ty, "(top)", 0, state.code.count);
        PatchAnnotations(ty);
}

static Scope *
load_module(Ty *ty, char const *name, Scope *scope)
{
        char *source = slurp_module(ty, name);

        if (source == NULL) {
                return NULL;
        }

        /*
         * Save the current compiler state so we can restore it after compiling
         * this module.
         */
        CompileState save = state;
        state = freshstate(ty);
        state.filename = name;

        compile(ty, source);

        Scope *module_scope;
        char *code = state.code.items;

        if (scope != NULL) {
                scope_copy_public(ty, scope, state.global, true);
                module_scope = scope;
        } else {
                module_scope = state.global;
                module_scope->external = true;

                struct module m = {
                        .path = name,
                        .code = code,
                        .scope = module_scope
                };

                avPn(m.imports, state.imports.items, state.imports.count);

                avP(modules, m);
        }

        state = save;

        // TODO: which makes more sense here?
        //emit_instr(ty, INSTR_EXEC_CODE);
        //emit_symbol(ty, (uintptr_t) m.code);
        vm_exec(ty, code);

        return module_scope;
}

bool
compiler_import_module(Ty *ty, Stmt const *s)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return false;
        }

        import_module(ty, s);

        RESTORE_JB;

        return true;
}

static void
import_module(Ty *ty, Stmt const *s)
{
        char const *name = s->import.module;
        char const *as = s->import.as;
        bool pub = s->import.pub;

        state.start = s->start;
        state.end = s->end;

        Scope *module_scope = get_module_scope(name);

        /* First make sure we haven't already imported this module, or imported another module
         * with the same local alias.
         *
         * e.g.,
         *
         * import foo
         * import foo
         *
         * and
         *
         * import foo as bar
         * import baz as bar
         *
         * are both errors.
         */
        for (int i = 0; i < state.imports.count; ++i) {
                if (strcmp(as, state.imports.items[i].name) == 0)
                        fail(ty, "there is already a module imported under the name '%s'", as);
                if (state.imports.items[i].scope == module_scope)
                        fail(ty, "the module '%s' has already been imported", name);
        }

        if (module_scope == NULL) {
                module_scope = load_module(ty, name, NULL);
        }

        char const **identifiers = (char const **)s->import.identifiers.items;
        char const **aliases = (char const **)s->import.aliases.items;
        int n = s->import.identifiers.count;

        bool everything = n == 1 && strcmp(identifiers[0], "..") == 0;

        if (everything) {
                char const *id = scope_copy_public(ty, state.global, module_scope, pub);
                if (id != NULL)
                        fail(ty, "module '%s' exports conflcting name '%s'", name, id);
        } else if (s->import.hiding) {
                char const *id = scope_copy_public_except(ty, state.global, module_scope, identifiers, n, pub);
                if (id != NULL)
                        fail(ty, "module '%s' exports conflcting name '%s'", name, id);
        } else for (int i = 0; i < n; ++i) {
                Symbol *s = scope_lookup(ty, module_scope, identifiers[i]);
                if (s == NULL || !s->public)
                        fail(ty, "module '%s' does not export '%s'", name, identifiers[i]);
                if (scope_lookup(ty, state.global, aliases[i]) != NULL)
                        fail(ty, "module '%s' exports conflicting name '%s'", name, identifiers[i]);
                scope_insert_as(ty, state.global, s, aliases[i])->public = pub;
        }

        avP(state.imports, ((struct import){ .name = as, .scope = module_scope, .pub = pub }));

        import_vector pubs = get_module_public_imports(name);
}

char const *
compiler_error(Ty *ty)
{
        return Error;
}

void
compiler_init(Ty *ty)
{
        tags_init(ty);

        state = freshstate(ty);
        global = state.global;
}

void
compiler_load_builtin_modules(Ty *ty)
{
        if (setjmp(jb) != 0) {
                fprintf(stderr, "Aborting, failed to load builtin modules: %s\n", compiler_error(ty));
                exit(1);
        }

        load_module(ty, "ffi", get_module_scope("ffi"));
        load_module(ty, "os", get_module_scope("os"));
        load_module(ty, "ty", get_module_scope("ty"));
}

char *
compiler_load_prelude(Ty *ty)
{
        if (setjmp(jb) != 0) {
                fprintf(stderr, "Aborting, failed to load prelude: %s\n", compiler_error(ty));
                exit(1);
        }

        state.filename = "(prelude)";
        compile(ty, slurp_module(ty, "prelude"));

        state.global = scope_new(ty, "(prelude)", state.global, false);

        state.imports.count = 0;

        return state.code.items;
}

int
gettag(Ty *ty, char const *module, char const *name)
{
        Symbol *sym = compiler_lookup(ty, module, name);
        if (!(sym != NULL && sym->cnst && sym->tag != -1)) {
                fprintf(stderr, "failed to find tag %s%s%s\n", module ? module : "", module ? "." : "", name);
                exit(1);
        }
        return sym->tag;
}

Symbol *
compiler_lookup(Ty *ty, char const *module, char const *name)
{
        Scope *mscope;

        if (module == NULL) {
                return scope_lookup(ty, state.global, name);
        } else if (mscope = get_module_scope(module), mscope != NULL) {
                return scope_lookup(ty, mscope, name);
        }

        return NULL;
}

/*
 * This name kind of sucks.
 */
void
compiler_introduce_symbol(Ty *ty, char const *module, char const *name)
{
        Scope *s;
        if (module == NULL) {
                s = global;
        } else {
                s = get_module_scope(module);

                if (s == NULL) {
                        ++builtin_modules;
                        s = scope_new(ty, module, global, false);
                        avP(modules, ((struct module){
                                .path = module,
                                .code = NULL,
                                .scope = s
                        }));
                }
        }

        Symbol *sym = addsymbol(ty, s, name);
        sym->public = true;
        sym->init = true;
        LOG("%s got index %d", name, sym->i);

        BuiltinCount += 1;
}

void
compiler_introduce_tag(Ty *ty, char const *module, char const *name)
{
        Scope *s;
        if (module == NULL) {
                s = global;
        } else {
                s = get_module_scope(module);

                if (s == NULL) {
                        ++builtin_modules;
                        s = scope_new(ty, module, NULL, false);
                        avP(modules, ((struct module){
                                .path = module,
                                .code = NULL,
                                .scope = s
                        }));
                }
        }

        Symbol *sym = addsymbol(ty, s, name);
        sym->public = true;
        sym->cnst = true;
        sym->init = true;
        sym->tag = tags_new(ty, name);
        LOG("tag %s got index %d", name, sym->i);

        BuiltinCount += 1;
}

char *
compiler_compile_source(Ty *ty, char const *source, char const *filename)
{
        vec_init(state.code);
        vec_init(state.selfs);
        vec_init(state.expression_locations);

        state.annotation = (ProgramAnnotation) {0};

        state.filename = filename;
        int symbol_count = scope_get_symbol(ty);

        if (setjmp(jb) != 0) {
                scope_set_symbol(ty, symbol_count);
                return NULL;
        }

        compile(ty, source);

        char *code = state.code.items;

        vec_init(state.code);

        return code;
}

int
compiler_symbol_count(Ty *ty)
{
        return scope_get_symbol(ty);
}

Location
compiler_find_definition(Ty *ty, char const *file, int line, int col)
{
        location_vector *locs = NULL;

        for (int i = 0; i < location_lists.count; ++i) {
                if (location_lists.items[i].count == 0)
                        continue;
                if (strcmp(file, location_lists.items[i].items[0].filename) != 0)
                        continue;
                locs = &location_lists.items[i];
                break;
        }

        if (locs == NULL) {
                return (Location) {0};
        }

        for (int i = 0; i < locs->count; ++i) {
                if (locs->items[i].e->type == EXPRESSION_IDENTIFIER &&
                    locs->items[i].start.line == line &&
                    locs->items[i].start.col == col) {
                        return (Location) {
                                .line = locs->items[i].e->symbol->loc.line,
                                .col = locs->items[i].e->symbol->loc.col,
                                .s = locs->items[i].e->symbol->file
                        };
                }
        }

        return (Location) {0};
}

Expr const *
compiler_find_expr(Ty *ty, char const *code)
{
        location_vector *locs = NULL;

        uintptr_t c = (uintptr_t) code;
        //printf("Looking for %lu\n", c);

        /*
         * First do a linear search for the group of locations which
         * contains this one.
         */
        for (int i = 0; i < location_lists.count; ++i) {
                if (location_lists.items[i].count == 0)
                        continue;

                if (c < location_lists.items[i].items[0].p_start)
                        continue;

                uintptr_t end = 0;
                for (int j = 0; j < location_lists.items[i].count; ++j)
                        if (location_lists.items[i].items[j].p_end > end)
                                end = location_lists.items[i].items[j].p_end;

                if (c >= end)
                        continue;

                locs = &location_lists.items[i];

                //printf("Found range (%lu, %lu)\n", locs->items[0].p_start, end);

                break;
        }

        if (locs == NULL) {
                return NULL;
        }

        int match_index = 0;
        ptrdiff_t match_width = PTRDIFF_MAX;

        for (int i = 0; i < locs->count; ++i) {
                if (c < locs->items[i].p_start)
                        continue;
                if (c >= locs->items[i].p_end)
                        continue;
                ptrdiff_t width = locs->items[i].p_end - locs->items[i].p_start;
                if (width < match_width) {
                        match_index = i;
                        match_width = width;
                }
        }

        if (c < locs->items[match_index].p_start || c >= locs->items[match_index].p_end) {
                return NULL;
        }

        //printf("Found: (%luu, %lu)\n",
        //       (uintptr_t)(locs->items[match_index].p_start),
        //       (uintptr_t)(locs->items[match_index].p_end));

        return locs->items[match_index].e;

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
compiler_get_completions(Ty *ty, char const *mod, char const *prefix, char **out, int max)
{
        int n = 0;

        if (mod == NULL) {
                n += scope_get_completions(ty, state.global, prefix, out + n, max - n);
                n += scope_get_completions(ty, global, prefix, out + n, max - n);
                return n;
        }

        for (int i = 0; i < state.imports.count; ++i) {
                if (module_match(state.imports.items[i].name, mod)) {
                        return n + scope_get_completions(ty, state.imports.items[i].scope, prefix, out + n, max - n);
                }
        }

        return 0;
}

bool
compiler_has_module(Ty *ty, char const *name)
{
        for (int i = 0; i < state.imports.count; ++i) {
                if (module_match(state.imports.items[i].name, name)) {
                        return true;
                }
        }

        return false;
}

int
compiler_global_count(Ty *ty)
{
        return (int)global->owned.count;
}

Symbol *
compiler_global_sym(Ty *ty, int i)
{
        return global->owned.items[i];
}

inline static char *
mkcstr(Ty *ty, Value const *v)
{
        char *s = amA(v->bytes + 1);

        memcpy(s, v->string, v->bytes);
        s[v->bytes] = '\0';

        return s;
}

uint32_t
source_register(Ty *ty, void const *src)
{
#if 0
        char const *s = ((Expr *)src)->start.s;
        if (s == NULL) s = "XXXXX";
        int line = ((Expr *)src)->start.line;
        XLOG("Register: %p -> %p: [%.*s] (%d)", src, *(void **)src, (int)strcspn(s, "\n"), s, line + 1);
#endif

        for (uint32_t i = 0; i < source_map.count; ++i) {
                if (source_map.items[i] == NULL) {
                        source_map.items[i] = (void *)src;
                        return i + 1;
                }
        }

        vec_nogc_push(source_map, (void *)src);

        return source_map.count;
}

void *
source_lookup(Ty *ty, uint32_t src)
{
        if (src == 0 || src > source_map.count) {
                return NULL;
        } else {
                return source_map.items[src - 1];
        }
}

void
source_forget_arena(void const *arena)
{
        for (uint32_t i = 0; i < source_map.count; ++i) {
                void **p = source_map.items[i];
                if (p != NULL && *p == arena) {
                        source_map.items[i] = NULL;
                } else if (p != NULL) {
                }
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
                        "item", tyexpr(ty, e->elements.items[i]),
                        "cond", (e->aconds.items[i] == NULL) ? NIL : tyexpr(ty, e->aconds.items[i]),
                        "optional", BOOLEAN(e->optional.items[i]),
                        NULL
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

        Scope *scope = state.macro_scope == NULL
                     ? state.global
                     : state.macro_scope;

        fixup_access(ty, scope, (Expr *)e, true);
        expedite_fun(ty, (Expr *)e, scope);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (e->namespace != NULL) {
                        v = vT(2);
                        v.items[0] = tyexpr(ty, e->namespace);
                        v.items[1] = vSs(e->identifier, strlen(e->identifier));
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TyMemberAccess);
                        break;
                }
                v = vTn(
                        "name", vSs(e->identifier, strlen(e->identifier)),
                        "module", (e->module == NULL) ? NIL : vSs(e->module, strlen(e->module)),
                        "constraint", (e->constraint == NULL) ? NIL : tyexpr(ty, e->constraint),
                        NULL
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyId);

                break;
        case EXPRESSION_MODULE:
        case EXPRESSION_NAMESPACE:
                if (e->parent != NULL) {
                        v = vT(2);
                        v.items[0] = tyexpr(ty, e->parent);
                        v.items[1] = vSs(e->name, strlen(e->name));
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TyMemberAccess);
                        break;
                } else {
                        v = vTn(
                                "name", vSs(e->name, strlen(e->name)),
                                "module", NIL,
                                "constraint", NIL,
                                NULL
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
                        "name",       vSs(e->identifier, strlen(e->identifier)),
                        "pattern",    tyexpr(ty, e->aliased),
                        "module",     (e->module == NULL) ? NIL : vSs(e->module, strlen(e->module)),
                        "constraint", (e->constraint == NULL) ? NIL : tyexpr(ty, e->constraint),
                        NULL
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyPatternAlias);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                v = vTn(
                        "name", vSs(e->identifier, strlen(e->identifier)),
                        "module", (e->module == NULL) ? NIL : vSs(e->module, strlen(e->module)),
                        NULL
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyNotNil);
                break;
        case EXPRESSION_RESOURCE_BINDING:
                v = tagged(
                        ty,
                        TyResource,
                        vTn(
                                "name", vSs(e->identifier, strlen(e->identifier)),
                                "module", (e->module == NULL) ? NIL : vSs(e->module, strlen(e->module)),
                                NULL
                        ),
                        NONE
                );
                break;
        case EXPRESSION_ARRAY:
                v = ARRAY(vA());
                NOGC(v.array);
                for (int i = 0; i < e->elements.count; ++i) {
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

                for (int i = 0; i < e->elements.count; ++i) {
                        vAp(avElems, tyaitem(ty, e, i));
                }

                v = vTn(
                        "items", ARRAY(avElems),
                        "pattern", tyexpr(ty, e->compr.pattern),
                        "iter", tyexpr(ty, e->compr.iter),
                        "cond", e->compr.cond == NULL ? NIL : tyexpr(ty, e->compr.cond),
                        NULL
                );

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, v.tags, TyArrayCompr);

                break;
        }
        case EXPRESSION_TAG_APPLICATION:
        {
                if (e->tagged->type == EXPRESSION_TUPLE) {
                        v = vT(e->tagged->es.count +  1);
                        for (int i = 0; i < e->tagged->es.count; ++i) {
                                v.items[i + 1] = tyexpr(ty, e->tagged->es.items[i]);
                        }
                } else {
                        v = vT(2);
                        v.items[1] = tyexpr(ty, e->tagged);
                }

                if (e->identifier != EmptyString) {
                        Expr *id = amA0(sizeof *id);
                        *id = *e;
                        id->type = EXPRESSION_IDENTIFIER;
                        v.items[0] = tyexpr(ty, id);
                } else {
                        v.items[0] = tagged(ty, TyValue, *e->constraint->v, NONE);
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
                                "name", e->name != NULL ? vSs(e->name, strlen(e->name)) : NIL,
                                "params", ARRAY(params),
                                "rt", e->return_type != NULL ? tyexpr(ty, e->return_type) : NIL,
                                "body", tystmt(ty, e->body),
                                "decorators", ARRAY(decorators),
                                NULL
                        ),
                        NONE
                );

                for (int i = 0; i < e->decorators.count; ++i) {
                        vAp(decorators, tyexpr(ty, e->decorators.items[i]));
                }

                for (int i = 0; i < e->params.count; ++i) {
                        Value name = vSs(e->params.items[i], strlen(e->params.items[i]));
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
                                        "constraint", e->constraints.items[i] != NULL ? tyexpr(ty, e->constraints.items[i]) : NIL,
                                        "default", e->dflts.items[i] != NULL ? tyexpr(ty, e->dflts.items[i]) : NIL,
                                        NULL
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
                v.items[0] = vSs(e->identifier, strlen(e->identifier));
                v.items[1] = tyexpr(ty, e->tagged);
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
                for (int i = 0; i < e->es.count; ++i) {
                        Value name = (e->names.items[i] == NULL)
                                   ? NIL
                                   : vSs(e->names.items[i], strlen(e->names.items[i]));
                        vAp(
                                v.array,
                                tagged(
                                        ty,
                                        TyRecordEntry,
                                        vTn(
                                                "item", tyexpr(ty, e->es.items[i]),
                                                "name", name,
                                                "cond", (e->tconds.items[i] == NULL) ? NIL : tyexpr(ty, e->tconds.items[i]),
                                                "optional", BOOLEAN(!e->required.items[i]),
                                                NULL
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
                for (int i = 0; i < e->es.count; ++i) {
                        vAp(v.array, tyexpr(ty, e->es.items[i]));
                        continue;
                        vAp(
                                v.array,
                                tagged(
                                        ty,
                                        TyRecordEntry,
                                        vTn(
                                                "item", tyexpr(ty, e->es.items[i]),
                                                "name", NIL,
                                                "cond", NIL,
                                                "optional", NIL,
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                OKGC(v.array);
                break;
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyRecord);
                break;
        case EXPRESSION_YIELD:
                v = ARRAY(vA());
                for (int i = 0; i < e->es.count; ++i) {
                        vAp(v.array, tyexpr(ty, e->es.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyYield);
                break;
        case EXPRESSION_THROW:
                v = tagged(ty, TyThrow, tyexpr(ty, e->throw), NONE);
                break;
        case EXPRESSION_MATCH:
                v = vT(2);
                v.items[0] = tyexpr(ty, e->subject);
                v.items[1] = ARRAY(vA());
                for (int i = 0; i < e->patterns.count; ++i) {
                        Value case_ = vT(2);
                        case_.items[0] = tyexpr(ty, e->patterns.items[i]);
                        case_.items[1] = tyexpr(ty, e->thens.items[i]);
                        vAp(
                                v.items[1].array,
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
                                "default", e->dflt != NULL ? tyexpr(ty, e->dflt) : NIL,
                                NULL
                        ),
                        NONE
                );
                NOGC(v.items[0].array);
                for (int i = 0; i < e->keys.count; ++i) {
                        vAp(
                                v.items[0].array,
                                tagged(
                                        ty,
                                        TyDictItem,
                                        tyexpr(ty, e->keys.items[i]),
                                        tyexpr(ty, e->values.items[i]),
                                        NONE
                                )
                        );
                }
                OKGC(v.items[0].array);
                break;
        case EXPRESSION_FUNCTION_CALL:
                v = vTn(
                        "func", tyexpr(ty, e->function),
                        "args", ARRAY(vA()),
                        NULL
                );
                for (int i = 0; i < e->args.count; ++i) {
                        vAp(
                                v.items[1].array,
                                tagged(
                                        ty,
                                        TyArg,
                                        vTn(
                                                "arg", tyexpr(ty, e->args.items[i]),
                                                "cond", e->fconds.items[i] != NULL ? tyexpr(ty, e->fconds.items[i]) : NIL,
                                                "name", NIL,
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                for (int i = 0; i < e->kws.count; ++i) {
                        vAp(
                                v.items[1].array,
                                tagged(
                                        ty,
                                        TyArg,
                                        vTn(
                                                "arg", tyexpr(ty, e->kwargs.items[i]),
                                                "cond", e->fkwconds.items[i] != NULL ? tyexpr(ty, e->fkwconds.items[i]) : NIL,
                                                "name", vSs(e->kws.items[i], strlen(e->kws.items[i])),
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyCall);
                break;
        case EXPRESSION_METHOD_CALL:
                v = vTn(
                        "object", tyexpr(ty, e->function),
                        "method", vSs(e->method_name, strlen(e->method_name)),
                        "args", ARRAY(vA()),
                        NULL
                );
                for (int i = 0; i < e->method_args.count; ++i) {
                        vAp(
                                v.items[2].array,
                                tagged(
                                        ty,
                                        TyArg,
                                        vTn(
                                                "arg", tyexpr(ty, e->method_args.items[i]),
                                                "cond", e->mconds.items[i] != NULL ? tyexpr(ty, e->mconds.items[i]) : NIL,
                                                "name", NIL,
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                for (int i = 0; i < e->method_kws.count; ++i) {
                        vAp(
                                v.items[2].array,
                                tagged(
                                        ty,
                                        TyArg,
                                        vTn(
                                                "arg", tyexpr(ty, e->method_kwargs.items[i]),
                                                // TODO conditional method kwargs
                                                "cond", NIL,
                                                "name", vSs(e->method_kws.items[i], strlen(e->method_kws.items[i])),
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyMethodCall);
                break;
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                v = vT(2);
                v.items[0] = tyexpr(ty, e->object);
                v.items[1] = vSs(e->member_name, strlen(e->member_name));
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyMemberAccess);
                break;
        case EXPRESSION_SUBSCRIPT:
                v = vT(2);
                v.items[0] = tyexpr(ty, e->container);
                v.items[1] = tyexpr(ty, e->subscript);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TySubscript);
                break;
        case EXPRESSION_SLICE:
                v = vT(4);
                v.items[0] = tyexpr(ty, e->slice.e);
                v.items[1] = tyexpr(ty, e->slice.i);
                v.items[2] = tyexpr(ty, e->slice.j);
                v.items[3] = tyexpr(ty, e->slice.k);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TySlice);
                break;
        case EXPRESSION_WITH:
                v = ARRAY(vA());
                for (int i = 0; i < e->with.defs.count; ++i) {
                        vAp(v.array, tystmt(ty, e->with.defs.items[i]));
                }
                v = tagged(
                        ty,
                        TyWith,
                        v,
                        tystmt(ty, e->with.block->statements.items[1]->try.s),
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
                v = vSs(e->string, strlen(e->string));
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyString);
                break;
        case EXPRESSION_SPECIAL_STRING:
                v = ARRAY(vA());
                gP(&v);

                vAp(v.array, vSs(e->strings.items[0], strlen(e->strings.items[0])));

                for (int i = 0; i < e->expressions.count; ++i) {
                        Value expr = tyexpr(ty, e->expressions.items[i]);
                        Value arg = tyexpr(ty, *v_(e->fmt_args, i));
                        if (e->fmts.items[i] == NULL) {
                                vAp(v.array, expr);
                        } else {
                                Value s = vSs(e->fmts.items[i], strlen(e->fmts.items[i]));
                                Value w = INTEGER(e->widths.items[i]);
                                vAp(v.array, QUADRUPLE(expr, s, w, arg));
                        }
                        vAp(v.array, vSs(e->strings.items[i + 1], strlen(e->strings.items[i + 1])));
                }

                gX();

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TySpecialString);

                break;
        case EXPRESSION_USER_OP:
                v = tagged(
                        ty,
                        TyUserOp,
                        vSs(e->op_name, strlen(e->op_name)),
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
                                "name", vSs(e->identifier, strlen(e->identifier)),
                                "module", (e->module == NULL) ? NIL : vSs(e->module, strlen(e->module)),
                                NULL
                        ),
                        NONE
                );
                break;
        case EXPRESSION_IFDEF:
                v = tagged(
                        ty,
                        TyIfDef,
                        vTn(
                                "name", vSs(e->identifier, strlen(e->identifier)),
                                "module", (e->module == NULL) ? NIL : vSs(e->module, strlen(e->module)),
                                NULL
                        ),
                        NONE
                );
                break;
        case EXPRESSION_TEMPLATE_HOLE:
                if (ty->stack.count > e->integer)
                        v = *vm_get(ty, e->integer);
                else
                        v = TAG(TyNil);
                break;
        case EXPRESSION_TEMPLATE_VHOLE:
                if (ty->stack.count > e->integer)
                        v = tagged(ty, TyValue, *vm_get(ty, e->integer), NONE);
                else
                        v = TAG(TyNil);
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
                v.items[0] = tyexpr(ty, s->target);
                v.items[1] = tyexpr(ty, s->value);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyLet);
                break;
        case STATEMENT_CLASS_DEFINITION:
                v = vTn(
                        "name", vSs(s->class.name, strlen(s->class.name)),
                        "super", s->class.super != NULL ? tyexpr(ty, s->class.super) : NIL,
                        "methods", ARRAY(vA()),
                        "getters", ARRAY(vA()),
                        "setters", ARRAY(vA()),
                        "statics", ARRAY(vA()),
                        "fields",  ARRAY(vA()),
                        NULL
                );
                for (int i = 0; i < s->class.methods.count; ++i) {
                        vAp(v.items[2].array, tyexpr(ty, s->class.methods.items[i]));
                }
                for (int i = 0; i < s->class.getters.count; ++i) {
                        vAp(v.items[3].array, tyexpr(ty, s->class.getters.items[i]));
                }
                for (int i = 0; i < s->class.setters.count; ++i) {
                        vAp(v.items[4].array, tyexpr(ty, s->class.setters.items[i]));
                }
                for (int i = 0; i < s->class.statics.count; ++i) {
                        vAp(v.items[5].array, tyexpr(ty, s->class.statics.items[i]));
                }
                for (int i = 0; i < s->class.fields.count; ++i) {
                        vAp(v.items[6].array, tyexpr(ty, s->class.fields.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyClass);
                break;
        case STATEMENT_DEFER:
                v = tyexpr(ty, s->expression);
                v.tags = tags_push(ty, v.tags, TyDefer);
                break;
        case STATEMENT_RETURN:
                v = vT(s->returns.count);
                for (int i = 0; i < s->returns.count; ++i) {
                        v.items[i] = tyexpr(ty, s->returns.items[i]);
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
                                "depth", INTEGER(s->depth),
                                NULL
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
                v.items[0] = tyexpr(ty, s->match.e);
                v.items[1] = ARRAY(vA());
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        Value case_ = vT(2);
                        case_.items[0] = tyexpr(ty, s->match.patterns.items[i]);
                        case_.items[1] = tystmt(ty, s->match.statements.items[i]);
                        vAp(
                                v.items[1].array,
                                case_
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyMatch);
                break;
        case STATEMENT_WHILE_MATCH:
                v = vT(2);
                v.items[0] = tyexpr(ty, s->match.e);
                v.items[1] = ARRAY(vA());
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        Value case_ = vT(2);
                        case_.items[0] = tyexpr(ty, s->match.patterns.items[i]);
                        case_.items[1] = tystmt(ty, s->match.statements.items[i]);
                        vAp(
                                v.items[1].array,
                                case_
                        );
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
                        "stop", s->each.stop != NULL ? tyexpr(ty, s->each.stop) : NIL,
                        NULL
                );

                for (int i = 0; i < s->each.target->es.count; ++i) {
                       vAp(ps, tyexpr(ty, s->each.target->es.items[i]));
                }

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyEach);

                break;
        }
        case STATEMENT_FOR_LOOP:
                v = tagged(ty, TyFor, vT(4), NONE);
                v.items[0] = tystmt(ty, s->for_loop.init);
                v.items[1] = tyexpr(ty, s->for_loop.cond);
                v.items[2] = tyexpr(ty, s->for_loop.next);
                v.items[3] = tystmt(ty, s->for_loop.body);
                break;
        case STATEMENT_BLOCK:
                v = ARRAY(vA());
                for (int i = 0; i < s->statements.count; ++i) {
                        vAp(v.array, tystmt(ty, s->statements.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyBlock);
                break;
        case STATEMENT_MULTI:
                v = ARRAY(vA());
                for (int i = 0; i < s->statements.count; ++i) {
                        vAp(v.array, tystmt(ty, s->statements.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyMulti);
                break;
        case STATEMENT_WHILE:
                v = vT(2);
                v.items[0] = typarts(ty, &s->While.parts);
                v.items[1] = tystmt(ty, s->While.block);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, TyWhile);
                break;
        case STATEMENT_IF:
                v = vT(3);
                v.items[0] = typarts(ty, &s->iff.parts);
                v.items[1] = tystmt(ty, s->iff.then);
                v.items[2] = s->iff.otherwise != NULL ? tystmt(ty, s->iff.otherwise) : NIL;
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, 0, s->iff.neg ? TyIfNot : TyIf);
                break;
        case STATEMENT_TRY:
        {
                Array *avCatches = vA();

                for (int i = 0; i < s->try.handlers.count; ++i) {
                        Value catch = vT(2);
                        catch.items[0] = tyexpr(ty, s->try.patterns.items[i]);
                        catch.items[1] = tystmt(ty, s->try.handlers.items[i]);
                        vAp(avCatches, catch);
                }

                v = tagged(
                        ty,
                        TyTry,
                        vTn(
                                "body", tystmt(ty, s->try.s),
                                "catches", ARRAY(avCatches),
                                "always", (s->try.finally == NULL) ? NIL : tystmt(ty, s->try.finally),
                                NULL
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
        Stmt *s = amA0(sizeof *s);
        Stmt *src = source_lookup(ty, v->src);

        s->arena = GetArenaAlloc(ty);

        //printf("cstmt(ty): %s\n", value_show_color(ty, v));

        if (src == NULL && wrapped_type(ty, v) == VALUE_TUPLE) {
                Value *src_val = tuple_get(v, "src");
                if (src_val != NULL) {
                        src = source_lookup(ty, src_val->src);
                }
        }

        if (src != NULL) {
                s->start = src->start;
                s->end = src->end;
                s->filename = src->filename;
        } else {
                s->start = state.mstart;
                s->end = state.mend;
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
                s->doc = NULL;
                s->target = NewExpr(ty, EXPRESSION_IDENTIFIER);
                s->target->identifier = mkcstr(ty, tuple_get(v, "name"));
                s->target->module = NULL;
                s->target->constraint = NULL;
                s->target->symbolized = false;
                break;
        }
        case TyClass:
        {
                s->type = STATEMENT_CLASS_DEFINITION;
                s->class.name = mkcstr(ty, tuple_get(v, "name"));
                s->class.doc = NULL;
                Value *super = tuple_get(v, "super");
                s->class.super = (super != NULL && super->type != VALUE_NIL) ? cexpr(ty, super) : NULL;
                Value *methods = tuple_get(v, "methods");
                Value *getters = tuple_get(v, "getters");
                Value *setters = tuple_get(v, "setters");
                Value *statics = tuple_get(v, "statics");
                Value *fields = tuple_get(v, "fields");
                if (methods != NULL) for (int i = 0; i < methods->array->count; ++i) {
                        avP(s->class.methods, cexpr(ty, &methods->array->items[i]));
                }
                if (getters != NULL) for (int i = 0; i < getters->array->count; ++i) {
                        avP(s->class.getters, cexpr(ty, &getters->array->items[i]));
                }
                if (setters != NULL) for (int i = 0; i < setters->array->count; ++i) {
                        avP(s->class.setters, cexpr(ty, &setters->array->items[i]));
                }
                if (statics != NULL) for (int i = 0; i < statics->array->count; ++i) {
                        avP(s->class.statics, cexpr(ty, &statics->array->items[i]));
                }
                if (fields != NULL) for (int i = 0; i < fields->array->count; ++i) {
                        avP(s->class.fields, cexpr(ty, &fields->array->items[i]));
                }
                break;
        }
        case TyIfNot:
                s->iff.neg =  true;
                goto If;
        case TyIf:
                s->iff.neg = false;
        If:
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

                vec_init(s->try.handlers);
                vec_init(s->try.patterns);

                Value *vBody = tuple_get(v, "body");
                Value *vCatches = tuple_get(v, "catches");
                Value *vFinally = tuple_get(v, "cleanup");

                if (vCatches->type != VALUE_ARRAY) {
                        fail(ty, "non-array `catches` in ty.Try construction: %s", value_show_color(ty, v));
                }

                s->try.s = cstmt(ty, vBody);
                s->try.finally = (vFinally == NULL || vFinally->type == VALUE_NIL) ? NULL : cstmt(ty, vFinally);

                for (int i = 0; i < vCatches->array->count; ++i) {
                        Value *catch = &vCatches->array->items[i];
                        if (catch->type != VALUE_TUPLE || catch->count != 2) {
                                fail(ty, "invalid `catches` entry in ty.Try construction: %s", value_show_color(ty, catch));
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
                vec_init(s->match.patterns);
                vec_init(s->match.statements);
                vec_init(s->match.conds);
                Value *cases = &v->items[1];
                for (int i = 0; i < cases->array->count; ++i) {
                        Value *_case = &cases->array->items[i];
                        avP(s->match.patterns, cexpr(ty, &_case->items[0]));
                        avP(s->match.statements, cstmt(ty, &_case->items[1]));
                        avP(s->match.conds, NULL);
                }
                break;
        }
        case TyWhileMatch:
        {
                s->type = STATEMENT_WHILE_MATCH;
                s->match.e = cexpr(ty, &v->items[0]);
                vec_init(s->match.patterns);
                vec_init(s->match.statements);
                vec_init(s->match.conds);
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
                vec_init(s->returns);
                if (wrapped_type(ty, v) == VALUE_TUPLE) {
                        for (int i = 0; i < v->count; ++i) {
                                avP(s->returns, cexpr(ty, &v->items[i]));
                        }
                } else {
                        Value v_ = unwrap(ty, v);
                        Expr *ret = cexpr(ty, &v_);
                        if (ret->type == EXPRESSION_LIST) {
                                avPn(s->returns, ret->es.items, ret->es.count);
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
                vec_init(s->statements);
                for (int i = 0; i < v->array->count; ++i) {
                        if (v->array->items[i].type == VALUE_NIL) {
                                fail(ty, "nil in block: %s", value_show_color(ty, v));
                        }
                        avP(s->statements, cstmt(ty, &v->array->items[i]));
                }
                break;
        case TyMulti:
                s->type = STATEMENT_MULTI;
                vec_init(s->statements);
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
                        fail(ty, "cexpr(ty) returned NULL: %s", value_show_color(ty, v));
                }
                if (s->filename == NULL && s->expression->filename != NULL) {
                        s->filename = s->expression->filename;
                        s->start = s->expression->start;
                        s->end = s->expression->end;
                }
                break;
        }

        s->origin = state.origin;

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

        e->arena = GetArenaAlloc(ty);

        if (src == NULL && wrapped_type(ty, v) == VALUE_TUPLE) {
                Value *src_val = tuple_get(v, "src");
                if (src_val != NULL) {
                        src = source_lookup(ty, src_val->src);
                }
        }

        XLOG("cexpr(): v = %s", VSC(v));

        if (src != NULL) {
                e->start = src->start;
                e->end = src->end;
                e->filename = src->filename;
        } else {
                e->start = state.mstart;
                e->end = state.mend;
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
                e->type = EXPRESSION_LIST;
                if (v->type != VALUE_ARRAY) {
                        goto Bad;
                }
                for (int i = 0; i < v->array->count; ++i) {
                        avP(e->es, cexpr(ty, &v->array->items[i]));
                }
                break;
        case TyExpr:
                return v->ptr;
        case TyValue:
        {
                Value *value = amA(sizeof *value);
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
        case TyId:
        {
                e->type = EXPRESSION_IDENTIFIER;
                e->identifier = mkcstr(ty, tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                Value *constraint = tuple_get(v, "constraint");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                e->constraint = (constraint != NULL && constraint->type != VALUE_NIL) ? cexpr(ty, constraint) : NULL;

                if (e->module == NULL && strcmp(e->identifier, "__line__") == 0) {
                        e->start = state.mstart;
                        e->end = state.mend;
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
                        *e = *t;
                }

                if (v->count < 2) {
                        goto Bad;
                } if (v->count == 2) {
                        e->tagged = cexpr(ty, &v->items[1]);
                } else {
                        e->tagged = NewExpr(ty, EXPRESSION_TUPLE);
                        for (int i = 1; i < v->count; ++i) {
                                avP(e->tagged->es, cexpr(ty, &v->items[i]));
                        }
                }

                break;
        }
        case TyString:
                e->type = EXPRESSION_STRING;
                e->string = mkcstr(ty, v);
                break;
        case TySpecialString:
        {
                e->type = EXPRESSION_SPECIAL_STRING;

                for (int i = 0; i < v->array->count; ++i) {
                        Value *x = &v->array->items[i];
                        if (x->type == VALUE_STRING) {
                                avP(e->strings, mkcstr(ty, x));
                        } else if (x->type == VALUE_TUPLE) {
                                avP(e->expressions, cexpr(ty, &x->items[0]));
                                avP(e->fmts, mkcstr(ty, &x->items[1]));
                                avP(e->widths, (x->count > 2) ? x->items[2].integer : 0);
                                avP(e->fmt_args, cexpr(ty, tget_nn(x, 3)));
                        } else {
                                avP(e->expressions, cexpr(ty, x));
                                avP(e->fmts, NULL);
                                avP(e->widths, 0);
                                avP(e->fmt_args, NULL);
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

                vec_init(e->elements);
                vec_init(e->aconds);
                vec_init(e->optional);

                for (int i = 0; i < v->array->count; ++i) {
                        Value *entry = &v->array->items[i];
                        Value *optional = tuple_get(entry, "optional");
                        Value *cond = tuple_get(entry, "cond");
                        avP(e->elements, cexpr(ty, tuple_get(entry, "item")));
                        avP(e->optional, optional != NULL ? optional->boolean : false);
                        avP(e->aconds, (cond != NULL && cond->type != VALUE_NIL) ? cexpr(ty, cond) : NULL);
                }

                break;
        }
        case TyRecord:
        {
                e->type = EXPRESSION_TUPLE;
                vec_init(e->es);
                vec_init(e->names);
                vec_init(e->required);
                vec_init(e->tconds);
                for (int i = 0; i < v->array->count; ++i) {
                        Value *entry = &v->array->items[i];
                        Value *item = tuple_get(entry, "item");
                        Value *name = tuple_get(entry, "name");
                        Value *optional = tuple_get(entry, "optional");
                        Value *cond = tuple_get(entry, "cond");
                        avP(e->es, cexpr(ty, item));
                        avP(e->names, name != NULL && name->type != VALUE_NIL ? mkcstr(ty, name) : NULL);
                        avP(e->required, optional != NULL ? !optional->boolean : true);
                        avP(e->tconds, cond != NULL && cond->type != VALUE_NIL ? cexpr(ty, cond) : NULL);
                }

                break;
        }
        case TyDict:
        {
                e->type = EXPRESSION_DICT;
                e->dtmp = NULL;
                vec_init(e->keys);
                vec_init(e->values);

                Value *items = tuple_get(v, "items");
                Value *dflt = tuple_get(v, "default");

                e->dflt = (dflt != NULL && dflt->type != VALUE_NIL) ? cexpr(ty, dflt) : NULL;

                for (int i = 0; i < items->array->count; ++i) {
                        avP(e->keys, cexpr(ty, &items->array->items[i].items[0]));
                        avP(e->values, cexpr(ty, &items->array->items[i].items[1]));
                }

                break;
        }
        case TyCall:
        {
                e->type = EXPRESSION_FUNCTION_CALL;
                vec_init(e->args);
                vec_init(e->fconds);
                vec_init(e->kws);
                vec_init(e->kwargs);
                vec_init(e->fkwconds);

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
        {
                e->type = EXPRESSION_METHOD_CALL;
                vec_init(e->method_args);
                vec_init(e->method_kws);
                vec_init(e->method_kwargs);
                vec_init(e->mconds);

                Value *maybe = tuple_get(v, "maybe");
                e->maybe = maybe != NULL && value_truthy(ty, maybe);

                Value *object = tuple_get(v, "object");
                e->object = cexpr(ty, object);

                Value *method = tuple_get(v, "method");
                e->method_name = mkcstr(ty, method);

                Value *args = tuple_get(v, "args");

                for (int i = 0; i < args->array->count; ++i) {
                        Value *arg = &args->array->items[i];
                        Value *cond = tget_nn(v, "cond");
                        Value *name = tget_t(v, "name", VALUE_STRING);

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
                e->ftype = FT_GEN;
                e->name = NULL;
                e->doc = NULL;
                e->proto = NULL;
                e->return_type = NULL;
                vec_init(e->params);
                vec_init(e->constraints);
                vec_init(e->dflts);
                vec_init(e->decorators);
                e->body = cstmt(ty, &v_);
                break;
        }
        case TyFunc:
        case TyImplicitFunc:
        {
                e->type = tag == TyFunc ? EXPRESSION_FUNCTION : EXPRESSION_IMPLICIT_FUNCTION;
                e->ikwargs = -1;
                e->rest = -1;
                e->ftype = FT_NONE;
                Value *name = tuple_get(v, "name");
                Value *params = tuple_get(v, "params");
                Value *rt = tuple_get(v, "rt");
                Value *decorators = tuple_get(v, "decorators");
                e->name = (name != NULL && name->type != VALUE_NIL) ? mkcstr(ty, name) : NULL;
                e->doc = NULL;
                e->proto = NULL;
                e->return_type = (rt != NULL && rt->type != VALUE_NIL) ? cexpr(ty, rt) : NULL;
                vec_init(e->params);
                vec_init(e->constraints);
                vec_init(e->dflts);
                vec_init(e->decorators);
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
                                avP(e->constraints, NULL);
                                avP(e->dflts, NULL);
                                e->rest = i;
                                break;
                        case TyKwargs:
                                avP(e->params, mkcstr(ty, p));
                                avP(e->constraints, NULL);
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
                Value *items = tuple_get(v, "items");

                if (pattern == NULL || iter == NULL)
                        goto Bad;

                e->type = EXPRESSION_ARRAY_COMPR;
                e->compr.pattern = cexpr(ty, pattern);
                e->compr.iter = cexpr(ty, iter);
                e->compr.cond = (cond == NULL || cond->type == VALUE_NIL) ? NULL : cexpr(ty, cond);

                vec_init(e->elements);
                vec_init(e->aconds);
                vec_init(e->optional);

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
        case TyMemberAccess:
                e->type = EXPRESSION_MEMBER_ACCESS;
                e->object = cexpr(ty, &v->items[0]);
                e->member_name = mkcstr(ty, &v->items[1]);
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
                vec_init(e->es);
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
                e->identifier = mkcstr(ty, tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                break;
        }
        case TyDefined:
        {
                e->type = EXPRESSION_DEFINED;
                e->identifier = mkcstr(ty, tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(ty, mod) : NULL;
                break;
        }
        case TyLet:
        case TyMatch:
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
                if (e->filename == NULL && e->statement->filename != NULL) {
                        e->filename = e->statement->filename;
                        e->start = e->statement->start;
                        e->end = e->statement->end;
                }
                break;
        default:
        Bad:
                fail(ty, "invalid value passed to cexpr(ty): %s", value_show_color(ty, v));
        }

        Scope *scope = state.macro_scope == NULL
                     ? state.global
                     : state.macro_scope;

        fixup_access(ty, scope, e, true);
        e->origin = state.origin;

        return e;
}

Value
CToTyExpr(Ty *ty, Expr *e)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return NONE;
        }

        Value v = tyexpr(ty, e);

        RESTORE_JB;

        return v;
}

Value
CToTyStmt(Ty *ty, Stmt *s)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return NONE;
        }

        Value v = tystmt(ty, s);

        RESTORE_JB;

        return v;
}

Expr *
TyToCExpr(Ty *ty, Value *v)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return NULL;
        }

        Expr *e = cexpr(ty, v);

        RESTORE_JB;

        return e;
}

Value
tyeval(Ty *ty, Expr *e)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return NONE;
        }

        if (!e->symbolized)
                symbolize_expression(ty, state.macro_scope, e);

        byte_vector code_save = state.code;
        vec_init(state.code);

        location_vector locs_save = state.expression_locations;
        vec_init(state.expression_locations);

        emit_expression(ty, e);
        emit_instr(ty, INSTR_HALT);

        RESTORE_JB;

        size_t n_location_lists = location_lists.count;

        add_location_info(ty);

        EvalDepth += 1;
        Value v = vm_try_exec(ty, state.code.items);
        EvalDepth -= 1;

        state.code = code_save;
        state.expression_locations = locs_save;

        location_lists.count = n_location_lists;

        return v;
}

Value
compiler_eval(
        Ty *ty,
        Expr *e
)
{
        symbolize_expression(ty, state.global, e);

        byte_vector code_save = state.code;
        vec_init(state.code);

        add_location_info(ty);
        vec_init(state.expression_locations);

        ProgramAnnotation annotation = state.annotation;
        state.annotation = (ProgramAnnotation) {0};

        emit_expression(ty, e);
        emit_instr(ty, INSTR_HALT);

        vec_init(state.expression_locations);

        vm_exec(ty, state.code.items);

        state.code = code_save;
        state.annotation = annotation;
        vec_init(state.expression_locations);

        Value v = *vm_get(ty, 0);
        vmX();

        return v;
}

Expr *
typarse(
        Ty *ty,
        Expr *e,
        Location const *start,
        Location const *end
)
{
        symbolize_expression(ty, state.global, e);

        byte_vector code_save = state.code;
        vec_init(state.code);

        add_location_info(ty);
        vec_init(state.expression_locations);

        ProgramAnnotation annotation = state.annotation;
        state.annotation = (ProgramAnnotation) {0};

        emit_expression(ty, e);
        emit_instr(ty, INSTR_HALT);

        vec_init(state.expression_locations);

        vm_exec(ty, state.code.items);

        state.code = code_save;
        state.annotation = annotation;
        vec_init(state.expression_locations);

        Value m = *vm_get(ty, 0);

        void *ctx = PushInfo(ty, NULL, "invoking macro %s", name_of(&m));

        Scope *macro_scope_save = state.macro_scope;
        state.macro_scope = state.global;

        Location const mstart = state.mstart;
        Location const mend = state.mend;
        state.mstart = *start;
        state.mend = *end;

        Value expr = vmC(&m, 0);
        vmP(&expr);

        state.macro_scope = macro_scope_save;

        Expr *e_ = cexpr(ty, &expr);

        state.mstart = mstart;
        state.mend = mend;

        // Take `m` and `expr` off the stack
        vmX();
        vmX();

        RestoreContext(ty, ctx);

        return e_;
}

void
define_tag(Ty *ty, Stmt *s)
{
        Scope *scope = GetNamespace(ty, s->ns);

        if (scope_locally_defined(ty, scope, s->class.name)) {
                fail(ty, "redeclaration of tag: %s", s->tag.name);
        }

        Symbol *sym = addsymbol(ty, scope, s->tag.name);
        sym->cnst = true;
        sym->init = true;
        sym->tag = tags_new(ty, s->tag.name);
        sym->doc = s->tag.doc;
        s->tag.symbol = sym->tag;
}

void
define_class(Ty *ty, Stmt *s)
{
        Scope *scope = GetNamespace(ty, s->ns);

        if (scope_locally_defined(ty, scope, s->class.name)) {
                fail(
                        ty,
                        "redeclaration of class %s%s%s%s%s",
                        TERM(1),
                        TERM(34),
                        s->class.name,
                        TERM(22),
                        TERM(39)
                );
        }

        Symbol *sym = addsymbol(ty, scope, s->class.name);
        sym->class = class_new(ty, s->class.name, s->class.doc);
        sym->doc = s->class.doc;
        sym->cnst = true;
        sym->init = true;
        s->class.symbol = sym->class;

        for (int i = 0; i < s->class.methods.count; ++i) {
                Expr *m = s->class.methods.items[i];

                // FIXME: we're doing the same check again in the CLASS_DEFINITION case of
                // symbolize_statement... we should probably just handle everything right here
                if (!contains(OperatorCharset, *m->name) || m->params.count == 0) {
                        class_add_method(ty, sym->class, m->name, PTR(m));
                }
        }
}

void
define_function(Ty *ty, Stmt *s)
{
        symbolize_lvalue(ty, GetNamespace(ty, s->ns), s->target, true, s->pub);
        s->target->symbol->doc = s->doc;
}

void
define_macro(Ty *ty, Stmt *s, bool fun)
{
        symbolize_statement(ty, state.global, s);
        if (fun)
                s->target->symbol->fun_macro = true;
        else
                s->target->symbol->macro = true;

        s->target->symbol->init = true;
        s->target->symbol->doc = s->doc;

        s->type = STATEMENT_FUNCTION_DEFINITION;

        add_location_info(ty);
        vec_init(state.expression_locations);

        byte_vector code_save = state.code;
        vec_init(state.code);

        ProgramAnnotation an = state.annotation;
        state.annotation = (ProgramAnnotation){0};

        emit_statement(ty, s, false);

        emit_instr(ty, INSTR_HALT);

        state.annotation = an;

        add_location_info(ty);
        vec_init(state.expression_locations);

        void *ctx = PushContext(ty, s);
        vm_exec(ty, state.code.items);
        RestoreContext(ty, ctx);

        state.code = code_save;
}

bool
is_fun_macro(Ty *ty, char const *module, char const *id)
{
        Symbol *s = NULL;

        if (module == NULL) {
                s = scope_lookup(ty, state.global, id);
        } else {
                Scope *mod = search_import_scope(module);
                if (mod != NULL) {
                        s = scope_lookup(ty, mod, id);
                }
        }

        return s != NULL && s->fun_macro;
}

bool
is_macro(Ty *ty, char const *module, char const *id)
{
        Symbol *s = NULL;

        if (module == NULL) {
                s = scope_lookup(ty, state.global, id);
        } else {
                Scope *mod = search_import_scope(module);
                if (mod != NULL) {
                        s = scope_lookup(ty, mod, id);
                }
        }

        return s != NULL && s->macro;
}

bool
compiler_symbolize_expression(Ty *ty, Expr *e, Scope *scope)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return false;
        }

        if (scope == NULL) {
                symbolize_expression(ty, state.global, e);
        } else {
                state.fscope = scope->function;
                symbolize_expression(ty, scope, e);
        }

        e->symbolized = true;

        RESTORE_JB;

        return true;
}

void
compiler_clear_location(Ty *ty)
{
        state.start = state.end = state.mstart = state.mend = Nowhere;
}

Value
compiler_render_template(Ty *ty, Expr *e)
{
        Value v;

        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                char const *msg = compiler_error(ty);
                v = Err(ty, vSs(msg, strlen(msg)));
                vmE(&v);
        }

        if (e->template.stmts.count == 1) {
                v = tystmt(ty, e->template.stmts.items[0]);
                goto End;
        }

        struct array *a = vA();

        for (size_t i = 0; i < e->template.stmts.count; ++i) {
                vAp(a, tystmt(ty, e->template.stmts.items[i]));
        }

        v = tagged(ty, TyMulti, ARRAY(a), NONE);

End:
        for (size_t i = 0; i < e->template.exprs.count; ++i) {
                vmX();
        }

        RESTORE_JB;

        return v;
}

void *
compiler_swap_jb(Ty *ty, void *jb)
{
        void *u = ujb;
        ujb = jb;
        return u;
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
                e == NULL ||
                e->type == EXPRESSION_STATEMENT ||
                e->type == STATEMENT_EXPRESSION
        ) {
                return 0;
        }

        return strlen(ExpressionTypeName(e));
}

int
WriteExpressionOrigin(Ty *ty, char *out, int cap, Expr const *e)
{
        char buffer[512];

        if (
                e == NULL ||
                e->type == EXPRESSION_STATEMENT ||
                e->type == STATEMENT_EXPRESSION
        ) {
                return 0;
        }

        char const *file = (e->filename == NULL) ? "(unknown)" : e->filename;
        int line = e->start.line;
        int col = e->start.col;

        if (e->type == EXPRESSION_CTX_INFO) {
                return snprintf(
                        out,
                        cap,
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

        int n = snprintf(
                out,
                cap,
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

        if (n < cap) n += snprintf(
                out + n,
                max(0, cap - n),
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

        if (n < cap) n += snprintf(
                out + n,
                max(0, cap - n),
                "\n%*s%s%s",
                before + 61,
                "",
                "",
                TERM(34)
        );

        for (int i = 0; i < length && n < cap; ++i)
                out[n++] = '^';

        if (n < cap) n += snprintf(
                out + n,
                cap - n,
                "%s%s",
                TERM(39),
                TERM(22)
        );

        if (cap > 0 && n >= cap) {
                out[cap - 1] = '\0';
        }

        return n;
}

char *
CompilationTrace(Ty *ty)
{
        vec(char) out = {0};
        char buffer[512];

        int etw = 0;
        for (ContextEntry *ctx = ContextList; ctx != NULL; ctx = ctx->next) {
                etw = max(etw, ExpressionTypeWidth(ctx->e));
        }

        for (ContextEntry *ctx = ContextList; ctx != NULL; ctx = ctx->next) {
                if (WriteExpressionTrace(ty, buffer, sizeof buffer, ctx->e, etw, ctx == ContextList) == 0) {
                        continue;
                }
                vec_nogc_push_n(out, buffer, strlen(buffer));
                if (WriteExpressionOrigin(ty, buffer, sizeof buffer, ctx->e->origin) == 0) {
                        continue;
                }
                vec_nogc_push_n(out, buffer, strlen(buffer));
        }

        vec_nogc_push(out, '\0');

        return out.items;
}

int
WriteExpressionTrace(Ty *ty, char *out, int cap, Expr const *e, int etw, bool first)
{
        char buffer[512];

        if (
                e == NULL ||
                e->type == EXPRESSION_STATEMENT ||
                e->type == STATEMENT_EXPRESSION
        ) {
                return 0;
        }

        char const *file = (e->filename == NULL) ? "(unknown)" : e->filename;
        int line = e->start.line;
        int col = e->start.col;

        if (e->type == EXPRESSION_CTX_INFO) {
                return snprintf(
                        out,
                        cap,
                        "%43s%s\n",
                        "",
                        e->string
                );
        }

        etw = min(etw, 24);
        int margin = 44 - etw;

        snprintf(
                buffer,
                sizeof buffer - 1,
                "%*s %s%s%s:%s%d%s:%s%d %s%*s%s",
                margin,
                first ? "at" : "from",
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

        int n = snprintf(
                out,
                cap,
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

        if (n < cap) n += snprintf(
                out + n,
                max(0, cap - n),
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

        if (n < cap) n += snprintf(
                out + n,
                max(0, cap - n),
                "\n%*s%s%s",
                before + 61,
                "",
                first ? TERM(1) : "",
                first ? TERM(91) : TERM(31)
        );

        for (int i = 0; i < length && n < cap; ++i)
                out[n++] = '^';

        if (n < cap) n += snprintf(
                out + n,
                cap - n,
                "%s%s",
                TERM(39),
                TERM(22)
        );

        if (cap > 0 && n >= cap) {
                out[cap - 1] = '\0';
        }

        return n;
}

char const *
NextCaption(ProgramAnnotation *annotation, char const *pc)
{
        while (
                annotation->i < annotation->map.count &&
                pc > annotation->map.items[annotation->i]
        ) {
                annotation->i += 1;
        }

        if (
                annotation->i == annotation->map.count ||
                pc != annotation->map.items[annotation->i]
        ) {
                return NULL;
        }

        return annotation->captions.items[annotation->i++];
}

char const *
DumpProgram(Ty *ty, byte_vector *out, char const *name, char const *code, char const *end)
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
            uintptr_t:   dump(out, " %"PRIuPTR, (x))                                       \
        )

        byte_vector after = {0};

#define DUMPSTR(s) (xvP(*out, ' '), dumpstr(out, (s)))
#define SKIPSTR()     (DUMPSTR(c), (c += strlen(c) + 1))
#define READSTR(s)    (((s) = c), SKIPSTR())
#define READVALUE(x)  (memcpy(&x, c, sizeof x), (c += sizeof x), PRINTVALUE(x))
#define READVALUE_(x) (memcpy(&x, c, sizeof x), (c += sizeof x))
#define READMEMBER(n) (READVALUE_((n)), DUMPSTR(M_NAME((n))))

        ProgramAnnotation *annotation = NULL;

        for (int i = 0; i < annotations.count; ++i) {
                if (
                        ((uintptr_t)code) >= annotations.items[i].start
                     && ((uintptr_t)code) <  annotations.items[i].end
                ) {
                        annotation = &annotations.items[i];
                        annotation->i = 0;
                }
        }

        if (code == NULL) {
                for (int i = 0; i < annotations.count; ++i) {
                        state.annotation = annotations.items[i];
                        DumpProgram(
                                ty,
                                out,
                                annotations.items[i].name,
                                (char const *)annotations.items[i].start,
                                (char const *)annotations.items[i].end
                        );
                }
                return end;
        }

        uintptr_t s;
        intmax_t k;
        bool b = false;
        double x;
        int n, nkw = 0, i, j, tag;

        dump(out, "%s%s:%s\n", TERM(34), name, TERM(0));
        dont_printf("        %s%s:%s\n", TERM(34), name, TERM(0));

        char const *caption;

        for (char const *c = code; c != end; xvP(*out, '\n')) {
                if (annotation != NULL) while (
                        (caption = NextCaption(annotation, c)) != NULL &&
                        caption[0] == ':'
                ) {
                        dump(out, "            %s%s:%s\n", TERM(95), caption + 1, TERM(0));
                        dont_printf("            %s%s:%s\n", TERM(95), caption + 1, TERM(0));
                }

                ptrdiff_t pc = (uintptr_t)c;
                ptrdiff_t begin = out->count;

#ifdef TY_ENABLE_PROFILING
                extern istat prof;
                extern FILE *ProfileOut;

                void
                color_sequence(float p, char *out);

                char color_buffer[64] = {0};
                istat_entry *stat = istat_lookup(&prof, c);

                int64_t max_ticks, total_ticks;
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
                dump(
                        out,
                        "                    %s%7td%s            %s%s%s",
                        TERM(94), pc, TERM(0),
                        TERM(93), GetInstructionName(*c), TERM(0)
                );
#endif

                dont_printf(
                        "%s%7td%s            %s%s%s %s\n",
                        TERM(94), pc, TERM(0),
                        TERM(93), GetInstructionName(*c), TERM(0),
                        name
                );

                switch ((unsigned char)*c++) {
                CASE(NOP)
                        break;
                CASE(LOAD_LOCAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        SKIPSTR();
#endif
                        break;
                CASE(LOAD_REF)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        SKIPSTR();
#endif
                        break;
                CASE(LOAD_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        SKIPSTR();
#endif

                        break;
                CASE(LOAD_GLOBAL)
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
                CASE(EXEC_CODE)
                        READVALUE(s);
                        break;
                CASE(DUP)
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
                CASE(TARGET_GLOBAL)
                        READVALUE(n);
                        break;
                CASE(TARGET_LOCAL)
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
                {
                        break;
                }
                CASE(POP_TRY)
                        break;
                CASE(RESUME_TRY)
                        break;
                CASE(CATCH)
                        break;
                CASE(TRY)
                {
                        READVALUE(n);
                        READVALUE(n);
                        READVALUE(n);
                        break;
                }
                CASE(DROP)
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
                        READVALUE(s);
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
                        break;
                CASE(TUPLE)
                        READVALUE(n);
                        while (n --> 0) {
                                READVALUE_(i);
                                switch (i) {
                                case -1: dump(out, " %s_%s", TERM(96),   TERM(0)); break;
                                case -2: dump(out, " %s*%s", TERM(95;1), TERM(0)); break;
                                default: DUMPSTR(M_NAME(i));
                                }
                        }
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
                        SKIPSTR();
                        READVALUE(n);
                        break;
                CASE(TO_STRING)
                        break;
                CASE(YIELD)
                        break;
                CASE(MAKE_GENERATOR)
                        break;
                CASE(VALUE)
                        READVALUE_(s);
                        dump(out, " %s", VSC((Value *)s));
                        dont_printf(" %s", VSC((Value *)s));
                        break;
                CASE(EVAL)
                        READVALUE(s);
                        break;
                CASE(RENDER_TEMPLATE)
                        READVALUE_(s);
                        xvP(*out, ' ');
                        dump_source_of((Expr *)s, out);
                        break;
                CASE(TRAP)
                        break;
                CASE(GET_NEXT)
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
                        break;
                CASE(CMP)
                        break;
                CASE(GET_TAG)
                        break;
                CASE(LEN)
                        break;
                CASE(PRE_INC)
                        break;
                CASE(POST_INC)
                        break;
                CASE(PRE_DEC)
                        break;
                CASE(POST_DEC)
                        break;
                CASE(MUT_ADD)
                        break;
                CASE(MUT_MUL)
                        break;
                CASE(MUT_DIV)
                        break;
                CASE(MUT_SUB)
                         break;
                CASE(BINARY_OP)
                        READVALUE_(n);
                        DUMPSTR(intern_entry(&xD.b_ops, n)->name);
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
                        int class, t, n, g, s;
                        READVALUE(class);
                        READVALUE(t);
                        READVALUE(n);
                        READVALUE(g);
                        READVALUE(s);
                        while (t --> 0) {
                                SKIPSTR();
                        }
                        while (n --> 0) {
                                SKIPSTR();
                        }
                        while (g --> 0) {
                                SKIPSTR();
                        }
                        while (s --> 0) {
                                SKIPSTR();
                        }
                        break;
                }
                CASE(FUNCTION)
                {
                        Value v;

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

                        char signature[256];

                        snprintf(
                                signature,
                                sizeof signature,
                                "%s%s",
                                name_of(&v),
                                (proto_of(&v) == NULL) ? "()" : proto_of(&v)
                        );

                        dump(out, " %s%s%s", TERM(96), signature, TERM(0));
                        c = DumpProgram(ty, &after, signature, c + hs, c + hs + size);

                        for (int i = 0; i < ncaps; ++i) {
                                READVALUE_(b);
                                READVALUE_(j);
                        }

                        break;
                }
                CASE(PATCH_ENV)
                        READVALUE(n);
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
                        READVALUE(n);
                        READMEMBER(n);
                        READVALUE(nkw);
                        for (int i = 0; i < nkw; ++i) {
                                SKIPSTR();
                        }
                        break;
                CASE(SAVE_STACK_POS)
                        break;
                CASE(RESTORE_STACK_POS)
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

                if (caption != NULL) {
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
        if (after.count > 0) {
                xvP(*out, '\n');
                xvPn(*out, after.items, after.count);
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

        return global == s
            || global == s->parent;
}

CompileState
PushCompilerState(Ty *ty, char const *filename)
{
        CompileState old = state;

        state = freshstate(ty);
        state.filename = filename;

        return old;
}

void
PopCompilerState(Ty *ty, CompileState saved)
{
        state = saved;
}

/* vim: set sw=8 sts=8 expandtab: */
