#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdnoreturn.h>

#include "location.h"
#include "log.h"
#include "alloc.h"
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

#define emit_instr(i) do { LOG("emitting instr: %s", #i); _emit_instr(i); } while (false)

#define PLACEHOLDER_JUMP(t, name) \
        emit_instr(t); \
        name = state.code.count; \
        emit_int(0);

#define PATCH_JUMP(name) \
        do { \
                jumpdistance = state.code.count - name - sizeof (int); \
                memcpy(state.code.items + name, &jumpdistance, sizeof jumpdistance); \
        } while (false)

#define JUMP(loc) \
        do { \
                emit_instr(INSTR_JUMP); \
                emit_int(loc - state.code.count - sizeof (int)); \
        } while (false)

#define JUMP_IF(loc) \
        do { \
                emit_instr(INSTR_JUMP_IF); \
                emit_int(loc - state.code.count - sizeof (int)); \
        } while (false)

#define JUMP_IF_NOT(loc) \
        do { \
                emit_instr(INSTR_JUMP_IF_NOT); \
                emit_int(loc - state.code.count - sizeof (int)); \
        } while (false)

#define SAVE_JB \
        jmp_buf jb_; \
        memcpy(&jb_, &jb, sizeof jb);

#define RESTORE_JB \
        memcpy(&jb, &jb_, sizeof jb);

#ifdef TY_ENABLE_PROFILING
#define KEEP_LOCATION(e) true
#else
#define KEEP_LOCATION(e) ((e)->type > EXPRESSION_KEEP_LOC)
#endif

#if 0
  #define INSTR_SAVE_STACK_POS INSTR_SAVE_STACK_POS), emit_int(__LINE__
  #define INSTR_RESTORE_STACK_POS INSTR_RESTORE_STACK_POS), emit_int(__LINE__
#endif

struct eloc {
        union {
                uintptr_t p_start;
                size_t start_off;
        };
        union {
                uintptr_t p_end;
                size_t end_off;
        };
        struct location start;
        struct location end;
        char const *filename;
        struct expression const *e;
};

struct import {
        bool pub;
        char const *name;
        struct scope *scope;
};

typedef vec(struct import)    import_vector;

struct module {
        char const *path;
        char *code;
        struct scope *scope;
        import_vector imports;
};

typedef vec(struct eloc)      location_vector;
typedef vec(struct symbol *)  symbol_vector;
typedef vec(size_t)           offset_vector;
typedef vec(offset_vector *)  jumplist_stack;
typedef vec(char)             byte_vector;
typedef vec(unsigned)         info_vector;

typedef struct loop_state {
        offset_vector continues;
        offset_vector breaks;
        int resources;
        int t;
        bool wr;
        bool each;
} LoopState;

typedef struct try_state {
        int t;
        bool finally;
} TryState;

typedef vec(LoopState) LoopStates;
typedef vec(TryState) TryStates;

/*
 * State which is local to a single compilation unit.
 */
struct state {
        byte_vector code;

        offset_vector selfs;
        offset_vector match_fails;
        offset_vector match_successes;
        offset_vector generator_returns;

        symbol_vector bound_symbols;

        int function_resources;
        int resources;

        struct scope *method;
        struct scope *fscope;

        struct scope *macro_scope;

        struct scope *implicit_fscope;
        struct expression *implicit_func;

        struct expression *func;
        int class;

        int function_depth;

        TryStates tries;
        LoopStates loops;

        import_vector imports;
        vec(char const *) exports;

        struct scope *global;

        char const *filename;
        struct location start;
        struct location end;

        struct location mstart;
        struct location mend;

        location_vector expression_locations;
};

bool CheckConstraints = true;
size_t GlobalCount = 0;

static jmp_buf jb;
static char const *Error;

static int builtin_modules;
static int BuiltinCount;

static int jumpdistance;
static vec(struct module) modules;
static struct state state;
static vec(location_vector) location_lists;
static vec(void *) source_map;
static struct scope *global;
static uint64_t t;
static char const EmptyString[] = { '\0', '\0' };
static struct location Nowhere = { 0, 0, EmptyString + 1 };

static void
symbolize_statement(struct scope *scope, struct statement *s);

static void
symbolize_pattern(struct scope *scope, struct expression *e, struct scope *reuse, bool def);

static void
symbolize_expression(struct scope *scope, struct expression *e);

static bool
emit_statement(struct statement const *s, bool want_result);

static void
emit_expression(struct expression const *e);

static void
emit_expr(struct expression const *e, bool need_loc);

static void
emit_assignment(struct expression *target, struct expression const *e, bool maybe, bool def);

static bool
emit_case(struct expression const *pattern, struct expression const *cond, struct statement const *s, bool want_result);

static bool
emit_catch(struct expression const *pattern, struct expression const *cond, struct statement const *s, bool want_result);

inline static void
emit_tgt(struct symbol const *s, struct scope const *scope, bool def);

static void
emit_return_check(struct expression const *f);

static struct scope *
get_import_scope(char const *);

static struct scope *
search_import_scope(char const *);

void
import_module(struct statement const *s);

static struct scope *
get_module_scope(char const *name);

static void
invoke_macro(struct expression *e, struct scope *scope);

static void
invoke_fun_macro(Scope *, Expr *e);

static void
emit_spread(struct expression const *e, bool nils);

static void
compile(char const *source);

#define X(t) #t
static char const *ExpressionTypeNames[] = {
        TY_EXPRESSION_TYPES
};
static char const *StatementTypeNames[] = {
        TY_STATEMENT_TYPES
};
#undef X

inline static int
wrapped_type(Value const *v)
{
        if (v->tags == 0 || tags_pop(v->tags) == 0) {
                return v->type & ~VALUE_TAGGED;
        } else {
                return v->type;
        }
}

inline static Value
unwrap(Value const *wrapped)
{
        Value v = *wrapped;

        if (v.tags != 0) {
                v.tags = tags_pop(v.tags);
        }

        if (v.tags == 0) {
                v.type &= ~VALUE_TAGGED;
        }

        return v;
}

char const *
ExpressionTypeName(Expr const *e)
{
        if (e->type == EXPRESSION_STATEMENT) {
                if (e->statement->type == STATEMENT_EXPRESSION) {
                        return ExpressionTypeName(e->statement->expression);
                } else {
                        return StatementTypeNames[e->statement->type];
                }
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

        snprintf(
                out,
                n == 0 ? 0 : n - 1,
                "%s%.*s%s%s%.*s%s%s%.*s%s",
                base_color,
                before,
                prefix,
                TERM(1),
                expr_color,
                length,
                start->s,
                TERM(0),
                base_color,
                after,
                suffix,
                TERM(0)
        );
}

noreturn static void
fail(char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        int sz = ERR_SIZE - 1;
        char *err = ERR;
        int n = snprintf(ERR, sz, "%s%sCompileError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));

        n += vsnprintf(err + n, sz - n, fmt, ap);
        va_end(ap);

        struct location start = state.start;
        struct location end = state.end;

        char buffer[512];

        snprintf(
                buffer,
                sizeof buffer - 1,
                "%36s %s%s%s:%s%d%s:%s%d%s",
                "at",
                TERM(34),
                state.filename,
                TERM(39),
                TERM(33),
                start.line + 1,
                TERM(39),
                TERM(33),
                start.col + 1,
                TERM(39)
        );

        char const *where = buffer;
        int m = strlen(buffer) - 6*strlen(TERM(00));

        while (m > 36) {
                m -= 1;
                where += 1;
        }

        n += snprintf(
                ERR + n,
                sz - n,
                "\n\n%s near: ",
                where
        );

        char const *prefix = start.s;

        while (prefix[-1] != '\0' && prefix[-1] != '\n')
                --prefix;

        while (isspace(prefix[0]))
                ++prefix;

        int before = start.s - prefix;
        int length = end.s - start.s;
        int after = strcspn(end.s, "\n");

        if (length == 0) {
                length = 1;
                end.s += 1;
        }

        n += snprintf(
                ERR + n,
                sz - n,
                "%s%.*s%s%s%.*s%s%s%.*s%s",
                TERM(32),
                before,
                prefix,
                TERM(1),
                TERM(91),
                length,
                start.s,
                TERM(32),
                TERM(22),
                after,
                end.s,
                TERM(39)
        );

        n += snprintf(
                ERR + n,
                sz - n,
                "\n%*s%s%s",
                before + 43,
                "",
                TERM(1),
                TERM(91)
        );

        for (int i = 0; i < length && n < sz; ++i)
                ERR[n++] = '^';

        n += snprintf(
                ERR + n,
                sz - n,
                "%s%s",
                TERM(39),
                TERM(22)
        );

        Error = ERR;

        longjmp(jb, 1);
}

static int
eloc_cmp(void const *a_, void const *b_)
{
        struct eloc *a = a_;
        struct eloc *b = b_;

        if (a->p_start < b->p_start) return -1;
        if (a->p_start > b->p_start) return  1;

        return 0;
}

char const *
show_expr_type(Expr const *e)
{
        Value v = tyexpr(e);

        if (v.type == VALUE_TAG) {
                return tags_name(v.tag);
        } else {
                //return value_show_color(&v);
                return tags_name(tags_first(v.tags));
        }
}

static char *
show_expr(struct expression const *e)
{
        char buffer[4096];
        colorize_code(TERM(93), TERM(0), &e->start, &e->end, buffer, sizeof buffer);
        return sclone_malloc(buffer);
}

inline static void
_emit_instr(char c)
{
        VPush(state.code, c);
}

static int
method_cmp(void const *a_, void const *b_)
{
        struct expression const *a = *(struct expression const **)a_;
        struct expression const *b = *(struct expression const **)b_;

        int o = (a->name == NULL || b->name == NULL) ? 0 : strcmp(a->name, b->name);

        return (o != 0) ? o : (a->t - b->t);
}

static char *
try_slurp_module(char const *name)
{
        char pathbuf[512];

        char const *home = getenv("HOME");

        if (home == NULL)
                home = getenv("USERPROFILE");

        if (home == NULL)
                fail("unable to get USERPROFILE / HOME from the environment");

        snprintf(pathbuf, sizeof pathbuf, "%s/.ty/%s.ty", home, name);

        char *source = slurp(pathbuf);
        if (source == NULL) {
                snprintf(pathbuf, sizeof pathbuf, "%s.ty", name);
                source = slurp(pathbuf);
        }

        return source;
}

static char *
slurp_module(char const *name)
{
        char *source = try_slurp_module(name);

        if (source == NULL) {
                fail("failed to load module: %s", name);
        }

        return source;
}

static void
add_location(struct expression const *e, size_t start_off, size_t end_off)
{
        if (e->start.line == -1 && e->start.col == -1)
                return;

        //printf("Location: (%zu, %zu) (%d) '%.*s'\n", start_off, end_off, e->type, (int)(e->end.s - e->start.s), e->start.s);

        VPush(
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
add_location_info(void)
{
        struct eloc *locs = state.expression_locations.items;
        for (int i = 0; i < state.expression_locations.count; ++i) {
                locs[i].p_start = (uintptr_t)(state.code.items + locs[i].start_off);
                locs[i].p_end = (uintptr_t)(state.code.items + locs[i].end_off);
        }

        qsort(state.expression_locations.items, state.expression_locations.count, sizeof (struct eloc), eloc_cmp);

        vec_nogc_push(location_lists, state.expression_locations);
}

inline static void
begin_finally(void)
{
        vec_last(state.tries)->finally = true;
}

inline static void
end_finally(void)
{
        vec_last(state.tries)->finally = false;
}

inline static bool
inside_finally(void)
{
        return state.tries.count != 0 && vec_last(state.tries)->finally;
}

inline static TryState *
get_try(int i)
{
        if (i < state.tries.count) {
                return vec_last(state.tries) - i;
        } else {
                return NULL;
        }
}

inline static void
begin_try(void)
{
        TryState try = {
                .t = ++t,
                .finally = false
        };

        VPush(state.tries, try);
}

inline static void
end_try(void)
{
        vec_pop(state.tries);
}

inline static LoopState *
get_loop(int i)
{
        if (i < state.loops.count) {
                return vec_last(state.loops) - i;
        } else {
                return NULL;
        }
}

inline static void
begin_loop(bool wr, bool each)
{
        LoopState loop = {
                .t = ++t,
                .resources = state.resources,
                .wr = wr,
                .each = each
        };

        VPush(state.loops, loop);
}

inline static void
end_loop(void)
{
        vec_pop(state.loops);
}

inline static bool
is_call(struct expression const *e)
{
        return e->type == EXPRESSION_METHOD_CALL || e->type == EXPRESSION_FUNCTION_CALL;
}

inline static bool
is_tag(struct expression const *e)
{
        assert(e->type == EXPRESSION_IDENTIFIER);

        struct scope const *scope = (e->module == NULL || *e->module == '\0') ? state.global : get_import_scope(e->module);
        struct symbol *sym = scope_lookup(scope, e->identifier);

        return sym != NULL && sym->tag != -1;
}

inline static bool
is_const(struct scope const *scope, char const *name)
{
        struct symbol const *s = scope_lookup(scope, name);

        return s != NULL && s->cnst;
}

static bool
is_variadic(struct expression const *e)
{
        int n = 0;
        struct expression * const *args = NULL;
        struct expression * const *conds = NULL;

        if (e->type == EXPRESSION_FUNCTION_CALL) {
                n = e->args.count;
                args = e->args.items;
                conds = e->fconds.items;
        } else if (e->type == EXPRESSION_METHOD_CALL) {
                n = e->method_args.count;
                args = e->method_args.items;
                conds = e->mconds.items;
        }

        for (int i = 0; i < n; ++i) {
                if (args[i] != NULL && (args[i]->type == EXPRESSION_SPREAD || conds[i] != NULL)) {
                        return true;
                }
        }

        return false;
}

inline static struct symbol *
addsymbol(struct scope *scope, char const *name)
{
        assert(name != NULL);

        LOG("Declaring %s in scope %s", name, scope_name(scope));

        if (scope_locally_defined(scope, name) && is_const(scope, name) &&
            (scope == state.global || scope == global) && strcmp(name, "_") != 0) {
                fail(
                        "redeclaration of variable %s%s%s%s%s",
                        TERM(1),
                        TERM(34),
                        name,
                        TERM(22),
                        TERM(39)
                );
        }

        struct symbol *s = scope_add(scope, name);
        s->file = state.filename;
        s->loc = state.start;

        if ((scope == global || scope == state.global) && isupper(name[0])) {
                VPush(state.exports, name);
        }

        LOG("adding symbol: %s -> %d", name, s->symbol);

        return s;
}

inline static struct symbol *
getsymbol(struct scope const *scope, char const *name, bool *local)
{
        if (strcmp(name, "_") == 0) {
                fail(
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
                        char *id = sclonea(b);
                        struct symbol *sym = addsymbol(state.implicit_fscope, id);
                        VPush(state.implicit_func->params, id);
                        VPush(state.implicit_func->param_symbols, sym);
                        VPush(state.implicit_func->dflts, NULL);
                        VPush(state.implicit_func->constraints, NULL);
                }
        }

        struct symbol *s = scope_lookup(scope, name);
        if (s == NULL) {
                fail(
                        "reference to undefined variable: %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        name,
                        TERM(0)
                );
        }

        if (s->scope->external && !s->public)
                fail("reference to non-public external variable '%s'", name);

        bool is_local = s->scope->function == scope->function;

        if (local != NULL)
                *local = is_local;

        return s;
}

inline static struct symbol *
tmpsymbol(struct scope *scope)
{
        static int i;
        static char idbuf[16];

        assert(i <= 9999999);

        sprintf(idbuf, "%d", i++);

        return scope_add(scope, sclonea(idbuf));
}

static struct state
freshstate(void)
{
        struct state s;

        vec_init(s.code);

        vec_init(s.selfs);
        vec_init(s.bound_symbols);

        vec_init(s.loops);
        vec_init(s.tries);
        vec_init(s.generator_returns);

        s.resources = 0;
        s.function_resources = 0;

        vec_init(s.imports);
        vec_init(s.exports);

        s.method = NULL;
        s.global = scope_new("(global)", global, false);
        s.fscope = NULL;
        s.class = -1;

        s.func = NULL;
        s.implicit_func = NULL;
        s.implicit_fscope = NULL;

        s.macro_scope = NULL;

        s.function_depth = 0;

        s.filename = NULL;
        s.start = s.end = s.mstart = s.mend = Nowhere;

        vec_init(s.expression_locations);

        return s;
}

inline static bool
is_loop(struct statement const *s)
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

inline static struct expression *
to_module_access(struct scope const *scope, struct expression const *e)
{
        static vec(char) mod = {0};
        mod.count = 0;

        VPush(mod, '\0');

        char const *name;
        struct location start = e->start;
        struct location end = e->end;

        if (e->type == EXPRESSION_MEMBER_ACCESS) {
                name = e->member_name;
                start = e->start;
                end = e->end;
        } else {
                name = e->method_name;
                start = e->object->start;
                end = e->object->end;
                while (*end.s != '\0' && *end.s != '(') {
                        end.s += 1;
                }
        }

        e = e->object;

        while (e->type == EXPRESSION_MEMBER_ACCESS) {
                VInsertN(mod, e->member_name, strlen(e->member_name), 0);
                VInsert(mod, '/', 0);
                e = e->object;
        }

        if (e->type != EXPRESSION_IDENTIFIER || e->module != NULL) {
                return NULL;
        }

        if (scope_lookup(scope, e->identifier) != NULL) {
                return NULL;
        }

        struct expression *id = Allocate(sizeof *id);
        *id = (struct expression){0};

        id->start = start;
        id->end = end;
        id->filename = state.filename;
        id->identifier = (char *)name;
        id->type = EXPRESSION_IDENTIFIER;

        VInsertN(mod, e->identifier, strlen(e->identifier), 0);

        struct scope *mod_scope = search_import_scope(mod.items);

        if (mod_scope != NULL) {
                id->module = sclonea(mod.items);
                id->symbol = getsymbol(mod_scope, name, &id->local);
                return id;
        } else {
                return NULL;
        }
}


static bool
fixup_module_access(Expr *e, struct scope *scope)
{
        if (
                e->type != EXPRESSION_METHOD_CALL &&
                e->type != EXPRESSION_MEMBER_ACCESS
        ) {
                return false;
        }

        Expr *mod_access = to_module_access(scope, e);

        if (mod_access == NULL) {
                return false;
        }

        if (e->type == EXPRESSION_METHOD_CALL) {
                struct expression fc = *e;

                fc.type = EXPRESSION_FUNCTION_CALL;
                fc.args = e->method_args;
                fc.kwargs = e->method_kwargs;
                fc.kws = e->method_kws;
                fc.fconds = e->mconds;

                vec_init(fc.fkwconds);
                for (size_t i = 0; i < fc.kws.count; ++i)
                        VPush(fc.fkwconds, NULL);

                fc.function = mod_access;

                *e = fc;
        } else {
                *e = *mod_access;
        }

        return true;
}

static struct scope *
search_import_scope(char const *name)
{
        for (int i = 0; i < state.imports.count; ++i)
                if (strcmp(name, state.imports.items[i].name) == 0)
                        return state.imports.items[i].scope;

        return NULL;
}

static struct scope *
get_import_scope(char const *name)
{
        struct scope *scope = search_import_scope(name);

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
apply_decorator_macros(struct scope *scope, struct expression **ms, int n)
{
        for (int i = 0; i < n; ++i) {
                if (
                        ms[i]->type == EXPRESSION_FUNCTION_CALL &&
                        ms[i]->function->type == EXPRESSION_IDENTIFIER
                ) {
                        symbolize_expression(scope, ms[i]->function);

                        if (!ms[i]->function->symbol->fun_macro) {
                                fail("non-FLM used as method decorator macro");
                        }

                        invoke_fun_macro(scope, ms[i]);

                        if (ms[i]->type != EXPRESSION_FUNCTION) {
                                fail("method decorator macro returned %s", ExpressionTypeName(ms[i]));
                        }
                }
        }
}

static void
symbolize_methods(struct scope *scope, struct expression **ms, int n)
{
        for (int i = 0; i < n; ++i) {
                ms[i]->is_method = true;
                symbolize_expression(scope, ms[i]);
        }
}

static struct expression *
mkmulti(char *name, bool setters)
{
        struct expression *multi = Allocate(sizeof *multi);
        *multi = (struct expression){0};

        multi->type = EXPRESSION_MULTI_FUNCTION;
        multi->name = name;
        multi->rest = setters ? -1 : 0;
        multi->ikwargs = -1;

        VPush(multi->params, "@");
        VPush(multi->constraints, NULL);
        VPush(multi->dflts, NULL);

        return multi;
}

static void
aggregate_overloads(expression_vector *ms, bool setters)
{
        int n = ms->count;

        qsort(ms->items, n, sizeof *ms->items, method_cmp);

        for (int i = 0; i + 1 < n; ++i) {
                if (strcmp(ms->items[i]->name, ms->items[i + 1]->name) != 0) {
                        continue;
                }

                char buffer[1024];
                struct expression *multi = mkmulti(ms->items[i]->name, setters);

                int m = 0;
                do {
                        ms->items[i + m]->is_overload = true;
                        snprintf(buffer, sizeof buffer - 1, "%s#%d", ms->items[i + m]->name, m + 1);
                        ms->items[i + m]->name = sclonea(buffer);
                        VPush(multi->functions, ms->items[i + m]);
                        m += 1;
                } while (i + m < n && strcmp(ms->items[i + m]->name, multi->name) == 0);

                VPush(*ms, multi);
        }
}

static void
add_captures(struct expression *pattern, struct scope *scope)
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

        pattern->match_symbol = addsymbol(scope, "_0");

        for (int i = 1; i <= n; ++i) {
                char const *nt = names;
                for (int j = 0; j < n_named; ++j) {
                        int capture_index = (nt[0] << 8) + nt[1];
                        nt += 2;

                        if (capture_index == i) {
                                /*
                                 * Don't think clone is necessary here...
                                 */
                                addsymbol(scope, nt);
                                goto NextCapture;
                        }
                }

                /*
                 * This is not a named capture group
                 */
                char id[16];
                sprintf(id, "_%d", i);
                addsymbol(scope, sclonea(id));
        NextCapture:
                ;
        }
}

static void
try_symbolize_application(struct scope *scope, struct expression *e)
{
        struct expression *mod_access = (e->type == EXPRESSION_METHOD_CALL) ? to_module_access(scope, e) : NULL;

        if (mod_access != NULL) {
                struct expression fc = *e;

                fc.type = EXPRESSION_FUNCTION_CALL;
                fc.args = e->method_args;
                fc.kwargs = e->method_kwargs;
                fc.kws = e->method_kws;
                fc.fconds = e->mconds;

                vec_init(fc.fkwconds);
                for (size_t i = 0; i < fc.kws.count; ++i)
                        VPush(fc.fkwconds, NULL);

                fc.function = mod_access;

                *e = fc;
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
                        symbolize_expression(scope, e->function);
                } else {
                        e->type = EXPRESSION_TAG_PATTERN;
                }
                if (tag_pattern || e->function->symbol->tag != -1) {
                        struct expression f = *e;
                        char *identifier = e->function->identifier;
                        char *module = e->function->module;
                        struct expression **tagged = e->args.items;
                        int tagc = e->args.count;
                        struct symbol *symbol = e->function->symbol;
                        if (!tag_pattern) {
                                e->type = EXPRESSION_TAG_APPLICATION;
                        }
                        e->identifier = identifier;
                        e->module = module;
                        e->symbol = symbol;
                        e->constraint = NULL;
                        if (tagc == 1 && tagged[0]->type != EXPRESSION_MATCH_REST) {
                                e->tagged = tagged[0];
                        } else {
                                struct expression *items = Allocate(sizeof *items);
                                *items = (struct expression){0};
                                items->type = EXPRESSION_TUPLE;
                                items->start = e->start;
                                items->end = e->end;
                                items->filename = state.filename;
                                vec_init(items->es);
                                vec_init(items->tconds);
                                vec_init(items->required);
                                vec_init(items->names);
                                for (int i = 0; i < tagc; ++i) {
                                        VPush(items->es, tagged[i]);
                                        VPush(items->tconds, NULL);
                                        VPush(items->required, true);
                                        VPush(items->names, NULL);
                                }
                                for (int i = 0; i < f.kws.count; ++i) {
                                        VPush(items->es, f.kwargs.items[i]);
                                        VPush(items->tconds, f.fkwconds.items[i]);
                                        VPush(items->required, true);
                                        VPush(items->names, f.kws.items[i]);
                                }
                                e->tagged = items;
                        }
                }
        } else if (e->type == EXPRESSION_TAG_APPLICATION) {
                e->symbol = getsymbol(
                        (e->module == NULL || *e->module == '\0') ? scope : get_import_scope(e->module),
                        e->identifier,
                        NULL
                );
        }
}

static void
symbolize_lvalue_(struct scope *scope, struct expression *target, bool decl, bool pub)
{
        state.start = target->start;
        state.end = target->end;

        if (target->symbolized)
                return;

        target->filename = state.filename;

        struct expression *mod_access;

        try_symbolize_application(scope, target);

        switch (target->type) {
        case EXPRESSION_RESOURCE_BINDING:
                if (strcmp(target->identifier, "_") == 0) {
                        target->identifier = gensym();
                }
        case EXPRESSION_SPREAD:
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_TAG_PATTERN:
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
                        symbolize_lvalue_(scope, target->tagged, decl, pub);
                }
                if (decl) {
                        if (target->module != NULL) {
                                scope = get_import_scope(target->module);
                                pub = true;
                        }
                        target->symbol = addsymbol(scope, target->identifier);
                        target->local = true;
                        symbolize_expression(scope, target->constraint);
                        if (pub) {
                                target->symbol->public = true;
                                //VPush(state.exports, target->identifier);
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

                        target->symbol = getsymbol(scope, target->identifier, &target->local);

                        if (target->symbol->cnst) {
                        ConstAssignment:
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
                        state.resources += 1;
                }
                break;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_expression(scope, target->left);
                symbolize_lvalue_(scope, target->right, decl, pub);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_lvalue_(scope, target->tagged, decl, pub);
                target->symbol = getsymbol(
                        ((target->module == NULL || *target->module == '\0') ? state.global : get_import_scope(target->module)),
                        target->identifier,
                        NULL
                );
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < target->elements.count; ++i)
                        symbolize_lvalue_(scope, target->elements.items[i], decl, pub);
                target->atmp = tmpsymbol(scope);
                break;
        case EXPRESSION_DICT:
                if (target->dflt != NULL) {
                        state.start = target->dflt->start;
                        state.end = target->dflt->end;
                        fail("unexpected default clause in dict destructuring");
                }
                for (int i = 0; i < target->keys.count; ++i) {
                        symbolize_expression(scope, target->keys.items[i]);
                        symbolize_lvalue_(scope, target->values.items[i], decl, pub);
                }
                target->dtmp = tmpsymbol(scope);
                break;
        case EXPRESSION_SUBSCRIPT:
                symbolize_expression(scope, target->container);
                symbolize_expression(scope, target->subscript);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                mod_access = to_module_access(scope, target);
                if (mod_access != NULL) {
                        *target = *mod_access;
                        goto ConstAssignment;
                } else {
                        symbolize_expression(scope, target->object);
                }
                break;
        case EXPRESSION_TUPLE:
                target->ltmp = tmpsymbol(scope);
        case EXPRESSION_LIST:
                for (int i = 0; i < target->es.count; ++i) {
                        symbolize_lvalue_(scope, target->es.items[i], decl, pub);
                }
                break;
        default:
                fail("unexpected %s in lvalue context", ExpressionTypeName(target));
        }

        target->symbolized = true;
}

static void
symbolize_lvalue(struct scope *scope, struct expression *target, bool decl, bool pub)
{
        symbolize_lvalue_(scope, target, decl, pub);

        if (state.resources > 0) {
                target->has_resources = true;
                state.resources = 0;
        }
}

static void
symbolize_pattern_(struct scope *scope, struct expression *e, struct scope *reuse, bool def)
{
        if (e == NULL)
                return;

        if (e->symbolized)
                return;

        e->filename = state.filename;

        try_symbolize_application(scope, e);

        if (e->type == EXPRESSION_IDENTIFIER && is_tag(e))
                goto Tag;

        state.start = e->start;
        state.end = e->end;

        struct symbol *existing;

        switch (e->type) {
        case EXPRESSION_RESOURCE_BINDING:
                if (strcmp(e->identifier, "_") == 0) {
                        e->identifier = gensym();
                }
        case EXPRESSION_IDENTIFIER:
                if (strcmp(e->identifier, "_") != 0 && (is_const(scope, e->identifier) || scope_locally_defined(scope, e->identifier) || e->module != NULL)) {
                        e->type = EXPRESSION_MUST_EQUAL;
                        struct scope *s = (e->module == NULL || *e->module == '\0') ? scope : get_import_scope(e->module);
                        e->symbol = getsymbol(s, e->identifier, NULL);
                } else {
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_ALIAS_PATTERN:
                        if (reuse != NULL && e->module == NULL && (existing = scope_local_lookup(reuse, e->identifier)) != NULL) {
                                e->symbol = existing;
                        } else {
                                e->symbol = def ? addsymbol(scope, e->identifier) : getsymbol(scope, e->identifier, NULL);
                        }
                        symbolize_expression(scope, e->constraint);
                }
                if (e->type == EXPRESSION_RESOURCE_BINDING) {
                        state.resources += 1;
                } else if (e->type == EXPRESSION_TAG_PATTERN) {
                        symbolize_pattern_(scope, e->tagged, reuse, def);
                } else if (e->type == EXPRESSION_ALIAS_PATTERN) {
                        symbolize_pattern_(scope, e->aliased, reuse, def);
                }
                e->local = true;
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < e->elements.count; ++i)
                        symbolize_pattern_(scope, e->elements.items[i], reuse, def);
                break;
        case EXPRESSION_DICT:
                for (int i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(scope, e->keys.items[i]);
                        symbolize_pattern_(scope, e->values.items[i], reuse, def);
                }
                break;
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        symbolize_pattern_(scope, e->es.items[i], reuse, def);
                }
                break;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_expression(scope, e->left);
                symbolize_pattern_(scope, e->right, reuse, def);
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
                e->symbol = addsymbol(scope, e->identifier);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_pattern_(scope, e->tagged, reuse, def);
                break;
        Tag:
                symbolize_expression(scope, e);
                e->type = EXPRESSION_MUST_EQUAL;
                break;
        case EXPRESSION_CHECK_MATCH:
                symbolize_pattern_(scope, e->left, reuse, def);
                symbolize_expression(scope, e->right);
                break;
        case EXPRESSION_REGEX:
                add_captures(e, scope);
                break;
        default:
                symbolize_expression(scope, e);
                break;
        }

        e->symbolized = true;
}

static void
symbolize_pattern(struct scope *scope, struct expression *e, struct scope *reuse, bool def)
{
        symbolize_pattern_(scope, e, reuse, def);

        if (state.resources > 0) {
                e->has_resources = true;
                state.resources = 0;
        }
}


static Expr *
expedite_fun(Expr *e, void *ctx)
{
        if (e->type != EXPRESSION_FUNCTION_CALL)
                return e;

        if (e->function->type != EXPRESSION_IDENTIFIER) {
                return e;
        }

        Symbol *sym = scope_lookup(ctx, e->function->identifier);

        if (sym == NULL) {
                return e;
        }

        symbolize_expression(ctx, e->function);

        if (e->function->symbol->fun_macro) {
                invoke_fun_macro(ctx, e);
        }

        return e;
}

static void
comptime(struct scope *scope, struct expression *e)
{
        symbolize_expression(scope, e->operand);
        struct value v = tyeval(e->operand);
        Location mstart = state.mstart;
        Location mend = state.mend;
        state.mstart = state.start;
        state.mend = state.end;
        *e = *cexpr(&v);
        symbolize_expression(scope, e);
        state.mstart = mstart;
        state.mend = mend;
}

static void
invoke_fun_macro(Scope *scope, struct expression *e)
{
        byte_vector code_save = state.code;
        vec_init(state.code);

        location_vector locs_save = state.expression_locations;
        vec_init(state.expression_locations);

        emit_expression(e->function);
        emit_instr(INSTR_HALT);

        add_location_info();

        vm_exec(state.code.items);

        state.expression_locations = locs_save;
        state.code = code_save;

        struct value m = *vm_get(0);
        vm_pop();

        ++GC_OFF_COUNT;

        struct value raw = ARRAY(value_array_new());

        vm_push(&raw);

        for (size_t i = 0;  i < e->args.count; ++i) {
                value_array_push(raw.array, PTR(e->args.items[i]));
                struct value v = tyexpr(e->args.items[i]);
                vm_push(&v);
        }


        struct value v = vm_call(&m, e->args.count + 1);

        struct location const mstart = state.mstart;
        struct location const mend = state.mend;

        state.mstart = e->start;
        state.mend = e->end;

        *e = *cexpr(&v);

        state.mstart = mstart;
        state.mend = mend;

        --GC_OFF_COUNT;
}

static void
symbolize_expression(struct scope *scope, struct expression *e)
{
        if (e == NULL)
                return;

        if (e->symbolized)
                return;

        e->filename = state.filename;

        state.start = e->start;
        state.end = e->end;

        struct scope *subscope;

        struct expression *func = state.func;
        struct expression *implicit_func = state.implicit_func;
        struct scope *implicit_fscope = state.implicit_fscope;
        struct expression *mod_access;

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
                                e->string = class_name(state.class);
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
                        struct symbol *sym = scope_lookup(scope, e->identifier);
                        if (sym == NULL || sym->scope == state.global || sym->scope == global) {
                                if (class_method(state.class, e->identifier)) {
                                        char const *id = e->identifier;
                                        e->type = EXPRESSION_SELF_ACCESS;
                                        e->member_name = id;
                                        e->maybe = false;
                                        e->object = Allocate(sizeof *e->object);
                                        *e->object = (struct expression){0};
                                        e->object->type = EXPRESSION_IDENTIFIER;
                                        e->object->identifier = "self";
                                        e->object->start = e->start;
                                        e->object->end = e->end;
                                        symbolize_expression(scope, e->object);
                                        break;
                                }
                        }
                }
                e->symbol = getsymbol(
                        ((e->module == NULL || *e->module == '\0') ? scope : get_import_scope(e->module)),
                        e->identifier,
                        &e->local
                );
                LOG("var %s local", e->local ? "is" : "is NOT");
                if (e->constraint != NULL) {
                        fail(
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
                comptime(scope, e);
                break;
        case EXPRESSION_SPECIAL_STRING:
                for (int i = 0; i < e->expressions.count; ++i)
                        symbolize_expression(scope, e->expressions.items[i]);
                break;
        case EXPRESSION_TAG:
                e->symbol = getsymbol(
                        ((e->module == NULL || *e->module == '\0') ? state.global : get_import_scope(e->module)),
                        e->identifier,
                        NULL
                );
                break;
        case EXPRESSION_TAG_APPLICATION:
                e->symbol = getsymbol(
                        ((e->module == NULL || *e->module) ? state.global : get_import_scope(e->module)),
                        e->identifier,
                        NULL
                );
                symbolize_expression(scope, e->tagged);
                break;
        case EXPRESSION_MATCH:
                symbolize_expression(scope, e->subject);
                for (int i = 0; i < e->patterns.count; ++i) {
                        struct scope *shared = scope_new("(match-shared)", scope, false);
                        if (e->patterns.items[i]->type == EXPRESSION_LIST) {
                                for (int j = 0; j < e->patterns.items[i]->es.count; ++j) {
                                        subscope = scope_new("(match-branch)", scope, false);
                                        symbolize_pattern(subscope, e->patterns.items[i]->es.items[j], shared, true);
                                        scope_copy(shared, subscope);
                                }
                                subscope = shared;
                        } else {
                                subscope = scope_new("(match-branch)", scope, false);
                                symbolize_pattern(subscope, e->patterns.items[i], NULL, true);
                        }
                        symbolize_expression(subscope, e->thens.items[i]);
                }
                break;
        case EXPRESSION_USER_OP:
                symbolize_expression(scope, e->sc);
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
        case EXPRESSION_KW_AND:
        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
                symbolize_expression(scope, e->left);
                symbolize_expression(scope, e->right);
                break;
        case EXPRESSION_DEFINED:
                e->type = EXPRESSION_BOOLEAN;
                if (e->module != NULL) {
                        struct scope *mscope = search_import_scope(e->module);
                        e->boolean = mscope != NULL && scope_lookup(mscope, e->identifier) != NULL;
                } else {
                        e->boolean = scope_lookup(scope, e->identifier) != NULL;
                }
                break;
        case EXPRESSION_IFDEF:
                if (e->module != NULL) {
                        struct scope *mscope = search_import_scope(e->module);
                        if (mscope != NULL && scope_lookup(mscope, e->identifier) != NULL) {
                                e->type = EXPRESSION_IDENTIFIER;
                                symbolize_expression(scope, e);
                                e->type = EXPRESSION_IFDEF;
                        } else {
                                e->type = EXPRESSION_NIL;
                        }
                } else {
                        if (scope_lookup(scope, e->identifier) != NULL) {
                                e->type = EXPRESSION_IDENTIFIER;
                                symbolize_expression(scope, e);
                                e->type = EXPRESSION_IFDEF;
                        } else {
                                e->type = EXPRESSION_NONE;
                        }
                }
                break;
        case EXPRESSION_EVAL:
                e->escope = scope;
                scope_capture_all(scope, global);
        case EXPRESSION_PREFIX_HASH:
        case EXPRESSION_PREFIX_BANG:
        case EXPRESSION_PREFIX_QUESTION:
        case EXPRESSION_PREFIX_MINUS:
        case EXPRESSION_PREFIX_AT:
        case EXPRESSION_PREFIX_INC:
        case EXPRESSION_PREFIX_DEC:
        case EXPRESSION_POSTFIX_INC:
        case EXPRESSION_POSTFIX_DEC:
                symbolize_expression(scope, e->operand);
                break;
        case EXPRESSION_CONDITIONAL:
                symbolize_expression(scope, e->cond);
                symbolize_expression(scope, e->then);
                symbolize_expression(scope, e->otherwise);
                break;
        case EXPRESSION_STATEMENT:
                symbolize_statement(scope, e->statement);
                break;
        case EXPRESSION_TEMPLATE:
                for (size_t i = 0; i < e->template.exprs.count; ++i) {
                        symbolize_expression(scope, e->template.exprs.items[i]);
                }
                break;
        case EXPRESSION_FUNCTION_CALL:
                symbolize_expression(scope, e->function);
                if (e->function->type == EXPRESSION_IDENTIFIER && e->function->symbol->fun_macro) {
                        invoke_fun_macro(scope, e);
                        symbolize_expression(scope, e);
                        break;
                }
                for (size_t i = 0;  i < e->args.count; ++i)
                        symbolize_expression(scope, e->args.items[i]);
                for (size_t i = 0;  i < e->args.count; ++i)
                        symbolize_expression(scope, e->fconds.items[i]);
                for (size_t i = 0; i < e->kwargs.count; ++i)
                        symbolize_expression(scope, e->kwargs.items[i]);
                break;
        case EXPRESSION_SUBSCRIPT:
                symbolize_expression(scope, e->container);
                symbolize_expression(scope, e->subscript);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                mod_access = to_module_access(scope, e);
                if (mod_access != NULL) {
                        *e = *mod_access;
                } else {
                        symbolize_expression(scope, e->object);
                }
                break;
        case EXPRESSION_METHOD_CALL:
                mod_access = to_module_access(scope, e);
                if (mod_access != NULL) {
                        struct expression fc = *e;

                        fc.type = EXPRESSION_FUNCTION_CALL;
                        fc.args = e->method_args;
                        fc.kwargs = e->method_kwargs;
                        fc.kws = e->method_kws;
                        fc.fconds = e->mconds;

                        vec_init(fc.fkwconds);
                        for (size_t i = 0; i < fc.kws.count; ++i)
                                VPush(fc.fkwconds, NULL);

                        fc.function = mod_access;

                        *e = fc;

                        symbolize_expression(scope, e);
                } else {
                        symbolize_expression(scope, e->object);
                        for (size_t i = 0;  i < e->method_args.count; ++i)
                                symbolize_expression(scope, e->method_args.items[i]);
                        for (size_t i = 0;  i < e->method_args.count; ++i)
                                symbolize_expression(scope, e->mconds.items[i]);
                        for (size_t i = 0; i < e->method_kwargs.count; ++i)
                                symbolize_expression(scope, e->method_kwargs.items[i]);
                }
                break;
        case EXPRESSION_EQ:
        case EXPRESSION_MAYBE_EQ:
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MINUS_EQ:
                symbolize_expression(scope, e->value);
                symbolize_lvalue(scope, e->target, false, false);
                break;
        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_FUNCTION:
                for (int i = 0; i < e->decorators.count; ++i) {
                        symbolize_expression(scope, e->decorators.items[i]);
                }

                state.func = e;

                if (e->name != NULL) {
                        scope = scope_new("(function name)", scope, false);
                        e->function_symbol = e->is_method ? NULL : addsymbol(scope, e->name);
                        LOG("== SYMBOLIZING %s ==", e->name);
                } else {
                        LOG("== SYMBOLIZING %s ==", "(anon)");
                        e->function_symbol = NULL;
                }

                scope = scope_new(e->name == NULL ? "(anon)" : e->name, scope, true);
                LOG("%s got scope %p (global=%p, state.global=%p)", e->name == NULL ? "(anon)" : e->name, scope, global, state.global);

                if (e->type == EXPRESSION_IMPLICIT_FUNCTION) {
                        state.implicit_fscope = scope;
                        state.implicit_func = e;
                        e->type = EXPRESSION_FUNCTION;
                }

                vec_init(e->param_symbols);

                for (size_t i = 0; i < e->params.count; ++i) {
                        symbolize_expression(scope, e->dflts.items[i]);
                        VPush(e->param_symbols, addsymbol(scope, e->params.items[i]));
                }

                /*
                 * This is trash.
                 */
                if (e->is_method) {
                        addsymbol(scope, "self");
                }

                for (size_t i = 0; i < e->params.count; ++i) {
                        symbolize_expression(scope, e->constraints.items[i]);
                }

                symbolize_expression(scope, e->return_type);

                symbolize_statement(scope, e->body);

                e->scope = scope;
                e->bound_symbols.items = scope->owned.items;
                e->bound_symbols.count = scope->owned.count;

                state.func = func;
                state.implicit_fscope = implicit_fscope;
                state.implicit_func = implicit_func;

                break;
        case EXPRESSION_WITH:
                subscope = scope_new("(with)", scope, false);
                symbolize_statement(subscope, e->with.block);
                for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                        for (struct symbol *sym = subscope->table[i]; sym != NULL; sym = sym->next) {
                                // Make sure it's not a tmpsymbol() symbol
                                if (!isdigit(sym->identifier[0])) {
                                        VPush(vec_last(e->with.block->statements)[0]->try.finally->drop, sym);
                                }
                        }
                }
                break;
        case EXPRESSION_THROW:
                symbolize_expression(scope, e->throw);
                break;
        case EXPRESSION_YIELD:
                for (int i = 0; i < e->es.count; ++i) {
                    symbolize_expression(scope, e->es.items[i]);
                }
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i) {
                        symbolize_expression(scope, e->elements.items[i]);
                        symbolize_expression(scope, e->aconds.items[i]);
                }
                break;
        case EXPRESSION_ARRAY_COMPR:
                symbolize_expression(scope, e->compr.iter);
                subscope = scope_new("(array compr)", scope, false);
                symbolize_lvalue(subscope, e->compr.pattern, true, false);
                symbolize_expression(subscope, e->compr.cond);
                for (size_t i = 0; i < e->elements.count; ++i) {
                        symbolize_expression(subscope, e->elements.items[i]);
                        symbolize_expression(subscope, e->aconds.items[i]);
                }
                break;
        case EXPRESSION_DICT:
                symbolize_expression(scope, e->dflt);
                for (size_t i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(scope, e->keys.items[i]);
                        symbolize_expression(scope, e->values.items[i]);
                }
                break;
        case EXPRESSION_DICT_COMPR:
                symbolize_expression(scope, e->dcompr.iter);
                subscope = scope_new("(dict compr)", scope, false);
                symbolize_lvalue(subscope, e->dcompr.pattern, true, false);
                symbolize_expression(subscope, e->dcompr.cond);
                for (size_t i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(subscope, e->keys.items[i]);
                        symbolize_expression(subscope, e->values.items[i]);
                }
                break;
        case EXPRESSION_LIST:
                for (int i = 0; i < e->es.count; ++i) {
                        symbolize_expression(scope, e->es.items[i]);
                }
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        symbolize_expression(scope, e->es.items[i]);
                        symbolize_expression(scope, e->tconds.items[i]);
                }
                break;
        case EXPRESSION_SPREAD:
        case EXPRESSION_SPLAT:
                symbolize_expression(scope, e->value);
                break;
        case EXPRESSION_MACRO_INVOCATION:
                invoke_macro(e, scope);
                break;
        case EXPRESSION_MATCH_REST:
                fail("*<identifier> 'match-rest' pattern used outside of pattern context");
        }

        e->symbolized = true;
}

static void
symbolize_statement(struct scope *scope, struct statement *s)
{
        if (s == NULL)
                return;

        state.start = s->start;
        state.end = s->end;

        struct scope *subscope;
        struct symbol *sym;

        switch (s->type) {
        case STATEMENT_IMPORT:
                import_module(s);
                break;
        case STATEMENT_EXPORT:
                VPushN(state.exports, s->exports.items, s->exports.count);
                break;
        case STATEMENT_DEFER:
                if (state.func == NULL) {
                        fail("invalid defer statement (not inside of a function)");
                }
                state.func->has_defer = true;
        case STATEMENT_EXPRESSION:
        case STATEMENT_BREAK:
        case STATEMENT_NEXT:
                symbolize_expression(scope, s->expression);
                break;
        case STATEMENT_CLASS_DEFINITION:
                if (!scope_locally_defined(state.global, s->class.name)) {
                        define_class(s);
                }

                if (s->class.super != NULL) {
                        symbolize_expression(scope, s->class.super);

                        if (s->class.super->symbol->class == -1)
                                fail("attempt to extend non-class");

                        class_set_super(s->class.symbol, s->class.super->symbol->class);

                        for (int i = 0; i < s->class.methods.count; ++i) {
                                struct expression *m = s->class.methods.items[i];
                                if (m->return_type == NULL) {
                                        struct value *v = class_method(s->class.super->symbol->class, m->name);
                                        if (v != NULL && v->type == VALUE_PTR) {
                                                m->return_type = ((struct expression *)v->ptr)->return_type;
                                        }
                                }
                        }
                } else {
                        class_set_super(s->class.symbol, 0);
                }

                subscope = scope_new(s->class.name, scope, false);
                state.class = s->class.symbol;

                apply_decorator_macros(subscope, s->class.methods.items, s->class.methods.count);
                apply_decorator_macros(subscope, s->class.getters.items, s->class.getters.count);
                apply_decorator_macros(subscope, s->class.setters.items, s->class.setters.count);
                apply_decorator_macros(subscope, s->class.statics.items, s->class.statics.count);

                aggregate_overloads(&s->class.methods, false);
                aggregate_overloads(&s->class.setters, true);
                aggregate_overloads(&s->class.statics, false);

                symbolize_methods(subscope, s->class.methods.items, s->class.methods.count);
                symbolize_methods(subscope, s->class.getters.items, s->class.getters.count);
                symbolize_methods(subscope, s->class.setters.items, s->class.setters.count);
                symbolize_methods(subscope, s->class.statics.items, s->class.statics.count);

                for (int i = 0; i < s->class.fields.count; ++i) {
                        Expr *field = s->class.fields.items[i];
                        switch (field->type) {
                        case EXPRESSION_IDENTIFIER:
                                symbolize_expression(subscope, field->constraint);
                                break;
                        case EXPRESSION_EQ:
                                if (field->target->type != EXPRESSION_IDENTIFIER) {
                                        field = field->target;
                                        goto BadField;
                                }
                                symbolize_expression(subscope, field->target->constraint);
                                break;
                        default:
                        BadField:
                                fail("invalid expression in field definition: %s", ExpressionTypeName(field));
                        }
                }

                state.class = -1;

                break;
        case STATEMENT_TAG_DEFINITION:
                if (scope_locally_defined(state.global, s->tag.name))
                        fail("redeclaration of tag: %s", s->tag.name);
                if (s->tag.super != NULL) {
                        symbolize_expression(scope, s->tag.super);
                        if (!is_tag(s->tag.super))
                                fail("attempt to extend non-tag");
                }
                sym = addsymbol(state.global, s->tag.name);
                sym->cnst = true;
                sym->tag = tags_new(s->tag.name);
                s->tag.symbol = sym->tag;
                subscope = scope_new(s->tag.name, scope, false);
                symbolize_methods(subscope, s->tag.methods.items, s->tag.methods.count);
                break;
        case STATEMENT_BLOCK:
                scope = scope_new("(block)", scope, false);

                for (size_t i = 0; i < s->statements.count; ++i) {
                        symbolize_statement(scope, s->statements.items[i]);
                }

                break;
        case STATEMENT_MULTI:
                for (size_t i = 0; i < s->statements.count; ++i) {
                        symbolize_statement(scope, s->statements.items[i]);
                }
                break;
        case STATEMENT_TRY:
        {
                symbolize_statement(scope, s->try.s);

                for (int i = 0; i < s->try.patterns.count; ++i) {
                        struct scope *catch = scope_new("(catch)", scope, false);
                        symbolize_pattern(catch, s->try.patterns.items[i], NULL, true);
                        symbolize_statement(catch, s->try.handlers.items[i]);
                }

                symbolize_statement(scope, s->try.finally);

                break;

        }
        case STATEMENT_WHILE_MATCH:
        case STATEMENT_MATCH:
                symbolize_expression(scope, s->match.e);
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        subscope = scope_new("(match)", scope, false);
                        symbolize_pattern(subscope, s->match.patterns.items[i], NULL, true);
                        symbolize_statement(subscope, s->match.statements.items[i]);
                }
                break;
        case STATEMENT_WHILE:
                subscope = scope_new("(while)", scope, false);
                for (int i = 0; i < s->While.parts.count; ++i) {
                        struct condpart *p = s->While.parts.items[i];
                        symbolize_expression(subscope, p->e);
                        symbolize_pattern(subscope, p->target, NULL, p->def);
                }
                symbolize_statement(subscope, s->While.block);
                break;
        case STATEMENT_IF:
                // if not let Ok(x) = f() or not [y] = bar() {
                subscope = scope_new("(if)", scope, false);
                if (s->iff.neg) {
                        symbolize_statement(scope, s->iff.then);
                        for (int i = 0; i < s->iff.parts.count; ++i) {
                                struct condpart *p = s->iff.parts.items[i];
                                symbolize_pattern(scope, p->target, NULL, p->def);
                                symbolize_expression(subscope, p->e);
                        }
                        symbolize_statement(subscope, s->iff.otherwise);
                } else {
                        symbolize_statement(subscope, s->iff.otherwise);
                        for (int i = 0; i < s->iff.parts.count; ++i) {
                                struct condpart *p = s->iff.parts.items[i];
                                symbolize_expression(subscope, p->e);
                                symbolize_pattern(subscope, p->target, NULL, p->def);

                        }
                        symbolize_statement(subscope, s->iff.then);
                }
                break;
        case STATEMENT_FOR_LOOP:
                scope = scope_new("(for)", scope, false);
                symbolize_statement(scope, s->for_loop.init);
                symbolize_expression(scope, s->for_loop.cond);
                symbolize_expression(scope, s->for_loop.next);
                symbolize_statement(scope, s->for_loop.body);
                break;
        case STATEMENT_EACH_LOOP:
                symbolize_expression(scope, s->each.array);
                subscope = scope_new("(for-each)", scope, false);
                symbolize_lvalue(subscope, s->each.target, true, false);
                symbolize_statement(subscope, s->each.body);
                symbolize_expression(subscope, s->each.cond);
                symbolize_expression(subscope, s->each.stop);
                break;
        case STATEMENT_RETURN:
                if (state.func == NULL) {
                        fail("invalid return statement (not inside of a function)");
                }

                for (int i = 0; i < s->returns.count; ++i) {
                    symbolize_expression(scope, s->returns.items[i]);
                }

                if (state.func->type == EXPRESSION_GENERATOR) {
                        s->type = STATEMENT_GENERATOR_RETURN;
                }

                break;
        case STATEMENT_DEFINITION:
                if (s->value->type == EXPRESSION_LIST) {
                        for (int i = 0; i < s->value->es.count; ++i) {
                                symbolize_expression(scope, s->value->es.items[i]);
                        }
                } else {
                        symbolize_expression(scope, s->value);
                }
                symbolize_lvalue(scope, s->target, true, s->pub);
                break;
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
                symbolize_lvalue(scope, s->target, true, s->pub);
                symbolize_expression(scope, s->value);
                break;
        }
}

static void
invoke_macro(struct expression *e, struct scope *scope)
{
        struct scope *macro_scope_save = state.macro_scope;
        state.macro_scope = scope;

        Arena old = NewArena(1 << 20);

        symbolize_expression(scope, e->macro.m);

        byte_vector code_save = state.code;
        vec_init(state.code);

        location_vector locs_save = state.expression_locations;
        vec_init(state.expression_locations);

        emit_expression(e->macro.m);
        emit_instr(INSTR_HALT);

        add_location_info();

        vm_exec(state.code.items);

        struct value m = *vm_get(0);
        vm_pop();

        state.code = code_save;
        state.expression_locations = locs_save;

        struct value node = tyexpr(e->macro.e);
        vm_push(&node);

        node = vm_call(&m, 1);

        state.macro_scope = macro_scope_save;

        struct expression *result = cexpr(&node);

        DestroyArena(old);

        symbolize_expression(scope, result);

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
patch_loop_jumps(size_t begin, size_t end)
{
        patch_jumps_to(&get_loop(0)->continues, begin);
        patch_jumps_to(&get_loop(0)->breaks, end);
}

inline static char
last_instr(void)
{
        return state.code.items[state.code.count - 1];
}

inline static void
emit_int(int k)
{
        LOG("emitting int: %d", k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (int); ++i)
                VPush(state.code, s[i]);
}

inline static void
emit_int16(int16_t k)
{
        LOG("emitting int16_t: %d", (int)k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (int16_t); ++i)
                VPush(state.code, s[i]);
}

inline static void
emit_ulong(unsigned long k)
{
        LOG("emitting ulong: %lu", k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (unsigned long); ++i)
                VPush(state.code, s[i]);
}

inline static void
emit_symbol(uintptr_t sym)
{
        LOG("emitting symbol: %"PRIuPTR, sym);
        char const *s = (char *) &sym;
        for (int i = 0; i < sizeof (uintptr_t); ++i)
                VPush(state.code, s[i]);
}

inline static void
emit_integer(intmax_t k)
{

        LOG("emitting integer: %"PRIiMAX, k);
        VPushN(state.code, (char const *)&k, sizeof k);
}

inline static void
emit_boolean(bool b)
{

        LOG("emitting boolean: %s", b ? "true" : "false");
        char const *s = (char *) &b;
        for (int i = 0; i < sizeof (bool); ++i)
                VPush(state.code, s[i]);
}

inline static void
emit_float(float f)
{

        LOG("emitting float: %f", f);
        VPushN(state.code, (char const *)&f, sizeof f);
}

inline static void
emit_string(char const *s)
{
        LOG("emitting string: %s", s);
        VPushN(state.code, s, strlen(s) + 1);
}

#ifndef TY_NO_LOG
#define emit_load_instr(id, inst, i) \
        do { \
                emit_instr(inst); \
                emit_int(i); \
                emit_string(id); \
        } while (0)
#else
#define emit_load_instr(id, inst, i) \
        do { \
                emit_instr(inst); \
                emit_int(i); \
        } while (0)
#endif

inline static void
target_captured(struct scope const *scope, struct symbol const *s)
{
        int i = 0;
        while (scope->function->captured.items[i] != s) {
                i += 1;
        }
        emit_instr(INSTR_TARGET_CAPTURED);
        emit_int(i);
#ifndef TY_NO_LOG
        emit_string(s->identifier);
#endif
}

inline static void
emit_load(struct symbol const *s, struct scope const *scope)
{
        LOG("Emitting LOAD for %s", s->identifier);

        bool local = !s->global && (s->scope->function == scope->function);

        if (s->global) {
                emit_load_instr(s->identifier, INSTR_LOAD_GLOBAL, s->i);
        } else if (local && !s->captured) {
                emit_load_instr(s->identifier, INSTR_LOAD_LOCAL, s->i);
        } else if (!local && s->captured) {
                LOG("It is captured and not owned by us");
                int i = 0;
                while (scope->function->captured.items[i] != s) {
                        i += 1;
                }
                emit_load_instr(s->identifier, INSTR_LOAD_CAPTURED, i);
        } else {
                emit_load_instr(s->identifier, INSTR_LOAD_REF, s->i);
        }
}

inline static void
emit_tgt(struct symbol const *s, struct scope const *scope, bool def)
{
        LOG("emit_tgt(%s, def=%d)", s->identifier, def);

        bool local = !s->global && (s->scope->function == scope->function);

        if (s->global) {
                emit_instr(INSTR_TARGET_GLOBAL);
                emit_int(s->i);
        } else if (def || (local && !s->captured)) {
                emit_instr(INSTR_TARGET_LOCAL);
                emit_int(s->i);
        } else if (!local && s->captured) {
                target_captured(scope, s);
        } else {
                emit_instr(INSTR_TARGET_REF);
                emit_int(s->i);
        }
}

static void
emit_list(struct expression const *e)
{
        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);

        if (e->type == EXPRESSION_LIST) for (int i = 0; i < e->es.count; ++i) {
                if (is_call(e->es.items[i])) {
                        emit_instr(INSTR_CLEAR_RC);
                        emit_expression(e->es.items[i]);
                        emit_instr(INSTR_GET_EXTRA);
                } else {
                        emit_expression(e->es.items[i]);
                }
        } else {
                emit_instr(INSTR_CLEAR_RC);
                emit_expression(e);
                emit_instr(INSTR_GET_EXTRA);
        }
}

static void
emit_constraint(struct expression const *c)
{
        size_t sc;
        emit_expression(c);
        emit_instr(INSTR_CHECK_MATCH);
        return;
        if (c->type == EXPRESSION_BIT_AND) {
                emit_instr(INSTR_DUP);
                emit_constraint(c->left);
                emit_instr(INSTR_DUP);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, sc);
                emit_instr(INSTR_POP);
                emit_constraint(c->right);
                PATCH_JUMP(sc);
        } else if (c->type == EXPRESSION_BIT_OR) {
                emit_instr(INSTR_DUP);
                emit_constraint(c->left);
                emit_instr(INSTR_DUP);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF, sc);
                emit_instr(INSTR_POP);
                emit_constraint(c->right);
                PATCH_JUMP(sc);
        } else {
                emit_expression(c);
                emit_instr(INSTR_CHECK_MATCH);
        }
}

static void
emit_function(struct expression const *e, int class)
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
        ++state.function_depth;

        LoopStates loops = state.loops;
        vec_init(state.loops);

        TryStates tries = state.tries;
        vec_init(state.tries);

        int t_save = t;
        t = 0;

        struct scope *fs_save = state.fscope;
        state.fscope = e->scope;

        struct expression *func_save = state.func;
        state.func = e;

        struct symbol **caps = e->scope->captured.items;
        int *cap_indices = e->scope->cap_indices.items;
        int ncaps = e->scope->captured.count;
        int bound_caps = 0;

        LOG("Compiling %s. scope=%s", e->name == NULL ? "(anon)" : e->name, scope_name(e->scope));

        for (int i = ncaps - 1; i >= 0; --i) {
                if (caps[i]->scope->function == e->scope) {
                        bound_caps += 1;
                } else if (cap_indices[i] == -1) {
                        /*
                         * Don't call emit_tgt because despite these being captured,
                         * we need to use TARGET_LOCAL to avoid following the reference.
                         */
                        emit_instr(INSTR_TARGET_LOCAL);
                        emit_int(caps[i]->i);
                } else {
                        // FIXME: should just use same allocated variable
                        LOG("%s: Using TARGET_CAPTURED for %s: %d", e->name == NULL ? "(anon)" : e->name, caps[i]->identifier, cap_indices[i]);
                        emit_instr(INSTR_TARGET_CAPTURED);
                        emit_int(cap_indices[i]);
#ifndef TY_NO_LOG
                        emit_string(caps[i]->identifier);
#endif
                }
        }

        emit_instr(INSTR_FUNCTION);

        while (((uintptr_t)(state.code.items + state.code.count)) % (_Alignof (int)) != ((_Alignof (int)) - 1))
                VPush(state.code, 0x00);
        VPush(state.code, 0xFF);

        emit_int(bound_caps);

        int bound = e->scope->owned.count;

        size_t hs_offset = state.code.count;
        emit_int(0);

        size_t size_offset = state.code.count;
        emit_int(0);

        emit_int(ncaps);
        emit_int(bound);
        emit_int(e->param_symbols.count);
        emit_int16(e->rest);
        emit_int16(e->ikwargs);

        for (int i = 0; i < sizeof (int) - 2 * sizeof (int16_t); ++i) {
                VPush(state.code, 0x00);
        }

        emit_int(class);

        // Need to GC code?
        VPush(state.code, 0);

        emit_symbol((uintptr_t)e->proto);
        emit_symbol((uintptr_t)e->doc);

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
                emit_string(buffer);
        } else {
                emit_string(e->name);
        }
#else
        emit_string(e->name == NULL ? "(anonymous function)" : e->name);
#endif

        LOG("COMPILING FUNCTION: %s", scope_name(e->scope));

        for (int i = 0; i < ncaps; ++i) {
                LOG(" => CAPTURES %s", caps[i]->identifier);
        }

        for (int i = 0; i < e->param_symbols.count; ++i) {
                emit_string(e->param_symbols.items[i]->identifier);
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
                struct symbol const *s = e->param_symbols.items[i];
                emit_load_instr(s->identifier, INSTR_LOAD_LOCAL, s->i);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NIL, size_t need_dflt);
                PLACEHOLDER_JUMP(INSTR_JUMP, size_t skip_dflt);
                PATCH_JUMP(need_dflt);
                emit_instr(INSTR_TARGET_LOCAL);
                emit_int(s->i);
                emit_expression(e->dflts.items[i]);
                emit_instr(INSTR_ASSIGN);
                emit_instr(INSTR_POP);
                PATCH_JUMP(skip_dflt);
        }

        for (int i = 0; i < e->param_symbols.count; ++i) {
                if (e->constraints.items[i] == NULL || (!e->is_overload && !CheckConstraints))
                        continue;
                struct symbol const *s = e->param_symbols.items[i];
                size_t start = state.code.count;
                emit_load_instr(s->identifier, INSTR_LOAD_LOCAL, s->i);
                emit_constraint(e->constraints.items[i]);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t good);
                if (e->is_overload) {
                        emit_instr(INSTR_POP);
                        emit_instr(INSTR_NONE);
                        emit_instr(INSTR_RETURN);
                } else {
                        emit_load_instr(s->identifier, INSTR_LOAD_LOCAL, s->i);
                        emit_instr(INSTR_BAD_CALL);
                        if (e->name != NULL)
                                emit_string(e->name);
                        else
                                emit_string("(anonymous function)");
                        emit_string(e->param_symbols.items[i]->identifier);
                        add_location(e->constraints.items[i], start, state.code.count);
                }
                emit_instr(INSTR_POP);
                PATCH_JUMP(good);
        }

        int function_resources = state.function_resources;
        state.function_resources = state.resources;

        struct statement *body = e->body;
        struct statement try;
        struct statement cleanup;

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
                emit_instr(INSTR_MAKE_GENERATOR);
                emit_statement(body, false);
                size_t end = state.code.count;
                emit_instr(INSTR_TAG);
                emit_int(TAG_NONE);
                emit_instr(INSTR_YIELD);
                emit_instr(INSTR_POP);
                JUMP(end);
                patch_jumps_to(&state.generator_returns, end);
        } else if (false && !emit_statement(body, false)) {
                /*
                 * Add an implicit 'return nil;' if the function
                 * doesn't explicitly return in its body.
                 */
                struct statement empty = {
                        .type = STATEMENT_RETURN,
                        .start = e->end,
                        .end = e->end
                };
                vec_init(empty.returns);
                emit_statement(&empty, false);
        } else if (e->type == EXPRESSION_MULTI_FUNCTION) {
                for (int i = 0; i < e->functions.count; ++i) {
                        if (!e->is_method) {
                                emit_instr(INSTR_SAVE_STACK_POS);
                                emit_load_instr("@", INSTR_LOAD_LOCAL, 0);
                                emit_spread(NULL, false);
                                emit_load_instr("", INSTR_LOAD_GLOBAL, ((struct statement *)e->functions.items[i])->target->symbol->i);
                                emit_instr(INSTR_CALL);
                                emit_int(-1);
                                emit_int(0);
                                emit_instr(INSTR_RETURN_IF_NOT_NONE);
                                emit_instr(INSTR_POP);
                        } else if (e->mtype == MT_SET) {
                                emit_load_instr("@", INSTR_LOAD_LOCAL, 0);
                                emit_load_instr("self", INSTR_LOAD_LOCAL, 1);
                                emit_instr(INSTR_TARGET_MEMBER);
                                emit_string(e->functions.items[i]->name);
                                emit_ulong(strhash(e->functions.items[i]->name));
                                emit_instr(INSTR_ASSIGN);
                                emit_instr(INSTR_RETURN_IF_NOT_NONE);
                                emit_instr(INSTR_POP);
                        } else {
                                emit_instr(INSTR_SAVE_STACK_POS);
                                emit_load_instr("@", INSTR_LOAD_LOCAL, 0);
                                emit_spread(NULL, false);
                                emit_load_instr("self", INSTR_LOAD_LOCAL, 1);
                                emit_instr(INSTR_CALL_METHOD);
                                emit_int(-1);
                                emit_string(e->functions.items[i]->name);
                                emit_ulong(strhash(e->functions.items[i]->name));
                                emit_int(0);
                                emit_instr(INSTR_RETURN_IF_NOT_NONE);
                                emit_instr(INSTR_POP);
                        }
                }
                emit_instr(INSTR_BAD_DISPATCH);
        } else {
                for (int i = ncaps - 1; i >= 0; --i) {
                        if (caps[i]->scope->function == e->scope) {
                                emit_instr(INSTR_CAPTURE);
                                emit_int(caps[i]->i);
                                emit_int(i);
                        }
                }
                emit_statement(body, true);
                if (CheckConstraints && e->return_type != NULL) {
                        emit_return_check(e);
                }
                emit_instr(INSTR_RETURN);
        }

        state.function_resources = function_resources;

        while ((state.code.count - start_offset) % P_ALIGN != 0) {
                VPush(state.code, 0x00);
        }

        int bytes = state.code.count - start_offset;
        memcpy(state.code.items + size_offset, &bytes, sizeof bytes);
        LOG("bytes in func = %d", bytes);

        for (int i = 0; i < ncaps; ++i) {
                if (caps[i]->scope->function == e->scope)
                        continue;
                bool local = caps[i]->scope->function == fs_save;
                LOG("local(%s, %s): %d", e->name == NULL ? "(anon)" : e->name, caps[i]->identifier, local);
                LOG("  fscope(%s) = %p, fs_save = %p", caps[i]->identifier, caps[i]->scope->function, fs_save);
                emit_boolean(local);
                emit_int(i);
        }

        state.fscope = fs_save;
        state.selfs = selfs_save;
        state.bound_symbols = syms_save;
        --state.function_depth;
        state.loops = loops;
        state.tries = tries;
        t = t_save;

        LOG("state.fscope: %s", scope_name(state.fscope));

        if (e->function_symbol != NULL) {
                emit_tgt(e->function_symbol, e->scope->parent, false);
                emit_instr(INSTR_ASSIGN);
        }

        state.func = func_save;

        for (int i = 0; i < e->decorators.count; ++i) {
                struct expression *c = e->decorators.items[i];
                if (c->type == EXPRESSION_FUNCTION_CALL) {
                        VInsert(c->args, NULL, 0);
                        VInsert(c->fconds, NULL, 0);
                } else {
                        VInsert(c->method_args, NULL, 0);
                        VInsert(c->mconds, NULL, 0);
                }
                emit_expression(c);
        }
}

static void
emit_and(struct expression const *left, struct expression const *right)
{
        emit_expression(left);
        emit_instr(INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t left_false);

        emit_instr(INSTR_POP);
        emit_expression(right);

        PATCH_JUMP(left_false);
}

static void
emit_or(struct expression const *left, struct expression const *right)
{
        emit_expression(left);
        emit_instr(INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t left_true);

        emit_instr(INSTR_POP);
        emit_expression(right);

        PATCH_JUMP(left_true);
}

static void
emit_coalesce(struct expression const *left, struct expression const *right)
{
        emit_expression(left);
        emit_instr(INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NIL, size_t left_nil);
        PLACEHOLDER_JUMP(INSTR_JUMP, size_t left_good);

        PATCH_JUMP(left_nil);

        emit_instr(INSTR_POP);
        emit_expression(right);

        PATCH_JUMP(left_good);
}

static void
emit_special_string(struct expression const *e)
{
        emit_instr(INSTR_STRING);
        emit_string(e->strings.items[0]);

        for (int i = 0; i < e->expressions.count; ++i) {
                emit_expression(e->expressions.items[i]);
                emit_instr(INSTR_TO_STRING);
                if (e->fmts.items[i] != NULL) {
                        VPushN(state.code, e->fmts.items[i], strcspn(e->fmts.items[i], "{"));
                }
                VPush(state.code, '\0');
                emit_instr(INSTR_STRING);
                emit_string(e->strings.items[i + 1]);
        }

        emit_instr(INSTR_CONCAT_STRINGS);
        emit_int(2 * e->expressions.count + 1);
}

static void
emit_with(struct expression const *e)
{
        emit_statement(e->with.block, true);
}

static void
emit_yield(struct expression const * const *es, int n, bool wrap)
{
        if (state.function_depth == 0) {
                fail("invalid yield expression (not inside of a function)");
        }

        if (n > 1) {
                fail("yielding multiple values isn't implemented yet");
        }

        for (int i = 0; i < n; ++i) {
                emit_expression(es[i]);
                if (wrap) {
                        emit_instr(INSTR_TAG_PUSH);
                        emit_int(TAG_SOME);
                }
        }

        emit_instr(INSTR_YIELD);
}

static void
emit_return_check(struct expression const *f)
{
        size_t start = state.code.count;

        emit_instr(INSTR_DUP);
        emit_constraint(f->return_type);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t good);
        emit_instr(INSTR_BAD_CALL);

        if (f->name != NULL)
                emit_string(f->name);
        else
                emit_string("(anonymous function)");

        emit_string("return value");

        add_location(f->return_type, start, state.code.count);

        PATCH_JUMP(good);
}

static bool
emit_return(struct statement const *s)
{
        if (inside_finally()) {
                fail("invalid return statement (occurs in a finally block)");
        }

        /* returning from within a for-each loop must be handled specially */
        for (int i = 0; i < state.loops.count; ++i) {
                if (get_loop(i)->each) {
                        emit_instr(INSTR_POP);
                        emit_instr(INSTR_POP);
                }
        }

        if (false && s->returns.count == 1 && is_call(s->returns.items[0])) {
                emit_instr(INSTR_TAIL_CALL);
        }

        if (s->returns.count > 0) for (int i = 0; i < s->returns.count; ++i) {
                emit_expression(s->returns.items[i]);
        } else {
                emit_instr(INSTR_NIL);
        }

        if (state.tries.count > 0) {
                emit_instr(INSTR_FINALLY);
        }

        for (int i = state.function_resources; i < state.resources; ++i) {
                emit_instr(INSTR_DROP);
        }

        if (CheckConstraints && state.func->return_type != NULL) {
                emit_return_check(state.func);
        }

        if (s->returns.count > 1) {
                emit_instr(INSTR_MULTI_RETURN);
                emit_int((int)s->returns.count - 1);
        } else {
                emit_instr(INSTR_RETURN);
        }

        return true;
}

static bool
emit_try(struct statement const *s, bool want_result)
{
        emit_instr(INSTR_TRY);

        size_t catch_offset = state.code.count;
        emit_int(0);

        size_t finally_offset = state.code.count;
        emit_int(-1);

        size_t end_offset = state.code.count;
        emit_int(-1);

        begin_try();

        if (s->type == STATEMENT_TRY_CLEAN) {
                emit_instr(INSTR_PUSH_DEFER_GROUP);
        }

        bool returns = emit_statement(s->try.s, want_result);

        PLACEHOLDER_JUMP(INSTR_JUMP, size_t end);

        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        PATCH_JUMP(catch_offset);

        for (int i = 0; i < s->try.patterns.count; ++i) {
                returns &= emit_catch(s->try.patterns.items[i], NULL, s->try.handlers.items[i], want_result);
        }

        emit_instr(INSTR_FINALLY);
        emit_instr(INSTR_RETHROW);

        patch_jumps_to(&state.match_successes, state.code.count);
        PATCH_JUMP(end);

        state.match_successes = successes_save;

        emit_instr(INSTR_FINALLY);

        end_try();

        if (s->try.finally != NULL) {
                PLACEHOLDER_JUMP(INSTR_JUMP, size_t end_real);
                PATCH_JUMP(finally_offset);
                begin_finally();
                returns &= emit_statement(s->try.finally, false);
                end_finally();
                PATCH_JUMP(end_offset);
                emit_instr(INSTR_HALT);
                PATCH_JUMP(end_real);
        } else {
                returns = false;
        }


        return returns;
}

static void
emit_for_loop(struct statement const *s, bool want_result)
{
        begin_loop(want_result, false);

        if (s->for_loop.init != NULL)
                emit_statement(s->for_loop.init, false);

        PLACEHOLDER_JUMP(INSTR_JUMP, size_t skip_next);

        size_t begin = state.code.count;

        if (s->for_loop.next != NULL) {
                emit_expression(s->for_loop.next);
                emit_instr(INSTR_POP);
        }

        PATCH_JUMP(skip_next);

        size_t end_jump = 0;
        if (s->for_loop.cond != NULL) {
                emit_expression(s->for_loop.cond);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, end_jump);
        }

        emit_statement(s->for_loop.body, false);

        JUMP(begin);

        if (s->for_loop.cond != NULL)
                PATCH_JUMP(end_jump);

        if (want_result)
                emit_instr(INSTR_NIL);

        patch_loop_jumps(begin, state.code.count);

        end_loop();
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
emit_record_rest(Expr const *rec, int i, bool is_assignment)
{
        emit_tgt(rec->es.items[i]->symbol, state.fscope, true);
        emit_instr(INSTR_RECORD_REST);

        size_t bad_assign_jump;

        if (!is_assignment) {
                VPush(state.match_fails, state.code.count);
        } else {
                bad_assign_jump = state.code.count;
        }

        // How far to jump in case this fails (i.e. the subject is not a record).
        // Overwritten later.
        emit_int(0);

        size_t sz_off = state.code.count;
        emit_int(0);

        VPush(state.code, '\0');
        for (int j = 0; j < i; ++j) {
                if (rec->names.items[j] != NULL) {
                        emit_string(rec->names.items[j]);
                }
        }

        PATCH_JUMP(sz_off);

        if (is_assignment) {
                emit_instr(INSTR_JUMP);
                emit_int(1);
                PATCH_JUMP(bad_assign_jump);
                emit_instr(INSTR_BAD_MATCH);
        }
}

static void
emit_try_match_(struct expression const *pattern)
{
        size_t start = state.code.count;
        bool need_loc = false;
        bool set = true;
        bool after = false;

        switch (pattern->type) {
        case EXPRESSION_RESOURCE_BINDING:
                emit_instr(INSTR_PUSH_DROP);
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_ALIAS_PATTERN:
                if (strcmp(pattern->identifier, "_") == 0) {
                        /* nothing to do */
                } else {
                        emit_tgt(pattern->symbol, state.fscope, true);
                        emit_instr(INSTR_ASSIGN);
                }
                if (pattern->constraint != NULL) {
                        emit_instr(INSTR_DUP);
                        emit_constraint(pattern->constraint);
                        emit_instr(INSTR_JUMP_IF_NOT);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
                }
                if (pattern->type == EXPRESSION_ALIAS_PATTERN) {
                        emit_try_match_(pattern->aliased);
                }
                break;
        case EXPRESSION_TAG_PATTERN:
                emit_tgt(pattern->symbol, state.fscope, true);
                emit_instr(INSTR_TRY_STEAL_TAG);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
                emit_try_match_(pattern->tagged);
                break;
        case EXPRESSION_CHECK_MATCH:
                emit_try_match_(pattern->left);
                emit_instr(INSTR_DUP);
                emit_constraint(pattern->right);
                emit_instr(INSTR_JUMP_IF_NOT);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_tgt(pattern->symbol, state.fscope, true);
                emit_instr(INSTR_TRY_ASSIGN_NON_NIL);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
                break;
        case EXPRESSION_MUST_EQUAL:
                emit_load(pattern->symbol, state.fscope);
                emit_instr(INSTR_ENSURE_EQUALS_VAR);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
                need_loc = true;
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                emit_instr(INSTR_DUP);
                emit_instr(INSTR_JUMP_IF_NIL);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
                // Fallthrough
        case EXPRESSION_VIEW_PATTERN:
                emit_instr(INSTR_DUP);
                emit_expression(pattern->left);
                emit_instr(INSTR_CALL);
                emit_int(1);
                emit_int(0);
                add_location(pattern->left, start, state.code.count);
                emit_try_match_(pattern->right);
                emit_instr(INSTR_POP);
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < pattern->elements.count; ++i) {
                        if (pattern->elements.items[i]->type == EXPRESSION_MATCH_REST) {
                                if (after) {
                                        state.start = pattern->elements.items[i]->start;
                                        state.end = pattern->elements.items[i]->end;
                                        fail("array pattern cannot contain multiple gather elements");
                                } else {
                                        after = true;
                                }
                                emit_tgt(pattern->elements.items[i]->symbol, state.fscope, true);
                                emit_instr(INSTR_ARRAY_REST);
                                emit_int(i);
                                emit_int(pattern->elements.count - i - 1);
                                VPush(state.match_fails, state.code.count);
                                emit_int(0);
                        } else {
                                emit_instr(INSTR_TRY_INDEX);
                                if (after) {
                                        if (pattern->optional.items[i]) {
                                                state.start = pattern->elements.items[i]->start;
                                                state.end = pattern->elements.items[i]->end;
                                                fail("optional element cannot come after a gather element in array pattern");
                                        }
                                        emit_int(i - pattern->elements.count);
                                } else {
                                        emit_int(i);
                                }
                                emit_boolean(!pattern->optional.items[i]);
                                VPush(state.match_fails, state.code.count);
                                emit_int(0);

                                emit_try_match_(pattern->elements.items[i]);

                                emit_instr(INSTR_POP);
                        }
                }

                if (!after) {
                        emit_instr(INSTR_ENSURE_LEN);
                        emit_int(pattern->elements.count);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
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
                        emit_expression(pattern);
                        emit_instr(INSTR_ENSURE_SAME_KEYS);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
                } else {
                        emit_instr(INSTR_ENSURE_DICT);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
                        for (int i = 0; i < pattern->keys.count; ++i) {
                                if (pattern->values.items[i] != NULL) {
                                        emit_instr(INSTR_DUP);
                                        emit_expression(pattern->keys.items[i]);
                                        emit_instr(INSTR_SUBSCRIPT);
                                        emit_try_match_(pattern->values.items[i]);
                                        emit_instr(INSTR_POP);
                                } else {
                                        emit_expression(pattern->keys.items[i]);
                                        emit_instr(INSTR_ENSURE_CONTAINS);
                                        VPush(state.match_fails, state.code.count);
                                        emit_int(0);
                                }
                        }
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_instr(INSTR_DUP);
                emit_instr(INSTR_TRY_TAG_POP);
                emit_int(pattern->symbol->tag);
                VPush(state.match_fails, state.code.count);
                emit_int(0);

                emit_try_match_(pattern->tagged);

                emit_instr(INSTR_POP);
                break;
        case EXPRESSION_REGEX:
                emit_tgt(pattern->match_symbol, state.fscope, true);
                emit_instr(INSTR_TRY_REGEX);
                emit_symbol((uintptr_t) pattern->regex);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
                need_loc = true;
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < pattern->es.count; ++i) {
                        if (pattern->es.items[i]->type == EXPRESSION_MATCH_REST) {
                                if (has_any_names(pattern)) {
                                        emit_record_rest(pattern, i, false);
                                } else {
                                        emit_tgt(pattern->es.items[i]->symbol, state.fscope, true);
                                        emit_instr(INSTR_TUPLE_REST);
                                        emit_int(i);
                                        VPush(state.match_fails, state.code.count);
                                        emit_int(0);

                                        if (i + 1 != pattern->es.count)
                                                fail("the *<id> tuple-matching pattern must be the last pattern in the tuple");
                                }
                        } else if (pattern->names.items[i] != NULL) {
                                emit_instr(INSTR_TRY_TUPLE_MEMBER);
                                emit_boolean(pattern->required.items[i]);
                                emit_string(pattern->names.items[i]);
                                VPush(state.match_fails, state.code.count);
                                emit_int(0);
                                emit_try_match_(pattern->es.items[i]);
                                emit_instr(INSTR_POP);
                        } else {
                                emit_instr(INSTR_TRY_INDEX_TUPLE);
                                emit_int(i);
                                VPush(state.match_fails, state.code.count);
                                emit_int(0);
                                emit_try_match_(pattern->es.items[i]);
                                emit_instr(INSTR_POP);
                        }
                }

                if (pattern->es.count == 0 || pattern->es.items[pattern->es.count - 1]->type != EXPRESSION_MATCH_REST) {
                        emit_instr(INSTR_ENSURE_LEN_TUPLE);
                        emit_int(pattern->es.count);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
                }

                break;
        case EXPRESSION_LIST:
                for (int i = 0; i < pattern->es.count; ++i) {
                        emit_instr(INSTR_PUSH_NTH);
                        emit_int(i);
                        emit_instr(INSTR_JUMP_IF_SENTINEL);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
                        emit_try_match_(pattern->es.items[i]);
                        emit_instr(INSTR_POP);
                }
                break;
        default:
                /*
                 * Need to think about how this should work...
                 */
                emit_instr(INSTR_DUP);
                emit_expression(pattern);
                //emit_instr(INSTR_CHECK_MATCH);
                emit_instr(INSTR_EQ);
                emit_instr(INSTR_JUMP_IF_NOT);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
                need_loc = true;
        }

        if (KEEP_LOCATION(pattern) || need_loc)
                add_location(pattern, start, state.code.count);
}

static void
emit_try_match(struct expression const *pattern)
{
        emit_try_match_(pattern);
}

static bool
emit_catch(struct expression const *pattern, struct expression const *cond, struct statement const *s, bool want_result)
{
        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        emit_instr(INSTR_SAVE_STACK_POS);
        emit_try_match(pattern);

        if (cond != NULL) {
                emit_expression(cond);
                emit_instr(INSTR_JUMP_IF_NOT);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
        }

        emit_instr(INSTR_RESTORE_STACK_POS);
        emit_instr(INSTR_CLEAR_EXTRA);

        bool returns = false;

        emit_instr(INSTR_CATCH);

        if (s != NULL) {
                returns = emit_statement(s, want_result);
        } else if (want_result) {
                emit_instr(INSTR_NIL);
        }

        emit_instr(INSTR_RESUME_TRY);

        emit_instr(INSTR_JUMP);
        VPush(state.match_successes, state.code.count);
        emit_int(0);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;

        return returns;
}

static bool
emit_case(struct expression const *pattern, struct expression const *cond, struct statement const *s, bool want_result)
{
        if (pattern->type == EXPRESSION_LIST) {
                bool returns = false;
                for (int i = 0; i < pattern->es.count; ++i) {
                        returns = emit_case(pattern->es.items[i], NULL, s, want_result);
                }
                return returns;
        }

        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        if (pattern->has_resources) {
                emit_instr(INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        emit_instr(INSTR_SAVE_STACK_POS);
        emit_try_match(pattern);

        if (cond != NULL) {
                emit_expression(cond);
                emit_instr(INSTR_JUMP_IF_NOT);
                VPush(state.match_fails, state.code.count);
                emit_int(0);
        }

        emit_instr(INSTR_RESTORE_STACK_POS);
        emit_instr(INSTR_CLEAR_EXTRA);

        bool returns = false;

        if (s != NULL) {
                returns = emit_statement(s, want_result);
        } else if (want_result) {
                emit_instr(INSTR_NIL);
        }

        if (pattern->has_resources) {
                emit_instr(INSTR_DROP);
                state.resources -= 1;
        }

        emit_instr(INSTR_JUMP);
        VPush(state.match_successes, state.code.count);
        emit_int(0);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;

        return returns;
}

static void
emit_expression_case(struct expression const *pattern, struct expression const *e)
{
        if (pattern->type == EXPRESSION_LIST) {
                for (int i = 0; i < pattern->es.count; ++i) {
                        emit_expression_case(pattern->es.items[i], e);
                }
                return;
        }

        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        if (pattern->has_resources) {
                emit_instr(INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        emit_instr(INSTR_SAVE_STACK_POS);
        emit_try_match(pattern);

        /*
         * Go back to where the subject of the match is on top of the stack,
         * then pop it and execute the code to produce the result of this branch.
         */
        emit_instr(INSTR_RESTORE_STACK_POS);
        emit_instr(INSTR_CLEAR_EXTRA);
        emit_expression(e);
        if (pattern->has_resources) {
                emit_instr(INSTR_DROP);
                state.resources -= 1;
        }

        /*
         * We've successfully matched a pattern+condition and produced a result, so we jump
         * to the end of the match expression. i.e., there is no fallthrough.
         */
        emit_instr(INSTR_JUMP);
        VPush(state.match_successes, state.code.count);
        emit_int(0);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;
}

static bool
emit_match_statement(struct statement const *s, bool want_result)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        /* FIXME: Why do we need a sentinel here? */
        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_expression(s->match.e);

        bool returns = true;

        for (int i = 0; i < s->match.patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                returns &= emit_case(s->match.patterns.items[i], NULL, s->match.statements.items[i], want_result);
        }

        /*
         * Nothing matched. This is a runtime errror.
         */
        emit_instr(INSTR_BAD_MATCH);

        patch_jumps_to(&state.match_successes, state.code.count);
        state.match_successes = successes_save;

        return returns;
}

static void
emit_while_match(struct statement const *s, bool want_result)
{
        begin_loop(want_result, false);

        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        size_t begin = state.code.count;

        emit_list(s->match.e);
        emit_instr(INSTR_FIX_EXTRA);

        for (int i = 0; i < s->match.patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                emit_case(s->match.patterns.items[i], NULL, s->match.statements.items[i], false);
        }

        /*
         * If nothing matches, we jump out of the loop.
         */
        emit_instr(INSTR_CLEAR_EXTRA);
        PLACEHOLDER_JUMP(INSTR_JUMP, size_t finished);

        /*
         * Something matched, so we iterate again.
         */
        patch_jumps_to(&state.match_successes, state.code.count);
        JUMP(begin);

        PATCH_JUMP(finished);

        if (want_result)
                emit_instr(INSTR_NIL);

        patch_loop_jumps(begin, state.code.count);

        state.match_successes = successes_save;

        end_loop();
}

static bool
emit_while(struct statement const *s, bool want_result)
{
        begin_loop(want_result, false);

        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        size_t start = state.code.count;

        bool has_resources = false;

        for (int i = 0; i < s->While.parts.count; ++i) {
                struct condpart *p = s->While.parts.items[i];
                if (p->target == NULL) {
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_expression(p->e);
                        emit_instr(INSTR_JUMP_IF_NOT);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
                        emit_instr(INSTR_RESTORE_STACK_POS);
                } else {
                        if (p->target->has_resources && !has_resources) {
                                emit_instr(INSTR_PUSH_DROP_GROUP);
                                state.resources += 1;
                                has_resources = true;
                        }
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_list(p->e);
                        emit_instr(INSTR_FIX_EXTRA);
                        emit_try_match(p->target);
                        emit_instr(INSTR_RESTORE_STACK_POS);
                }
        }

        emit_statement(s->While.block, false);

        if (has_resources) {
                emit_instr(INSTR_DROP);
                state.resources -= 1;
        }

        JUMP(start);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        if (want_result) {
                emit_instr(INSTR_NIL);
        }

        patch_loop_jumps(start, state.code.count);

        end_loop();

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        return false;
}

static bool
emit_if_not(struct statement const *s, bool want_result)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        bool has_resources = false;

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (p->target != NULL && p->target->has_resources) {
                        has_resources = true;
                        break;
                }
        }

        if (has_resources) {
                emit_instr(INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (p->target == NULL) {
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_expression(p->e);
                        emit_instr(INSTR_JUMP_IF);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
                        emit_instr(INSTR_RESTORE_STACK_POS);
                } else {
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_list(p->e);
                        emit_instr(INSTR_FIX_EXTRA);
                        emit_try_match(p->target);
                        emit_instr(INSTR_RESTORE_STACK_POS);
                }
        }

        bool returns = false;

        if (s->iff.otherwise != NULL) {
                returns |= emit_statement(s->iff.otherwise, want_result);
        } else if (want_result) {
                emit_instr(INSTR_NIL);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, size_t done);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        returns &= emit_statement(s->iff.then, want_result);

        PATCH_JUMP(done);

        if (has_resources) {
                emit_instr(INSTR_DROP);
                state.resources -= 1;
        }

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        return returns;
}

static bool
emit_if(struct statement const *s, bool want_result)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        /* Special case for 'if not' */
        if (s->iff.neg) {
                struct condpart *p = s->iff.parts.items[0];

                emit_list(p->e);
                emit_instr(INSTR_FIX_EXTRA);

                bool returns = emit_case(p->target, NULL, s->iff.otherwise, want_result);
                emit_instr(INSTR_CLEAR_EXTRA);
                returns &= emit_statement(s->iff.then, want_result);

                patch_jumps_to(&state.match_successes, state.code.count);
                state.match_successes = successes_save;

                return returns;
        }

        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        bool has_resources = false;

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (p->target != NULL && p->target->has_resources) {
                        has_resources = true;
                        break;
                }
        }

        if (has_resources) {
                emit_instr(INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (p->target == NULL) {
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_expression(p->e);
                        emit_instr(INSTR_JUMP_IF_NOT);
                        VPush(state.match_fails, state.code.count);
                        emit_int(0);
                        emit_instr(INSTR_RESTORE_STACK_POS);
                } else {
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_list(p->e);
                        emit_instr(INSTR_FIX_EXTRA);
                        emit_try_match(p->target);
                        emit_instr(INSTR_RESTORE_STACK_POS);
                }
        }

        bool returns = emit_statement(s->iff.then, want_result);
        PLACEHOLDER_JUMP(INSTR_JUMP, size_t done);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        if (s->iff.otherwise != NULL) {
                returns &= emit_statement(s->iff.otherwise, want_result);
        } else {
                if (want_result) {
                        emit_instr(INSTR_NIL);
                }
                returns = false;
        }

        PATCH_JUMP(done);

        if (has_resources) {
                emit_instr(INSTR_DROP);
                state.resources -= 1;
        }

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        return returns;
}

static void
emit_match_expression(struct expression const *e)
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
         * This applies to emit_match_statement() as well.
         */
        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_expression(e->subject);

        for (int i = 0; i < e->patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                emit_expression_case(e->patterns.items[i], e->thens.items[i]);
        }

        /*
         * Nothing matched. This is a runtime errror.
         */
        emit_instr(INSTR_BAD_MATCH);

        /*
         * If a branch matched successfully, it will jump to this point
         * after it is evaluated so as not to fallthrough to the other
         * branches.
         */
        patch_jumps_to(&state.match_successes, state.code.count);

        state.match_successes = successes_save;
}

static void
emit_target(struct expression *target, bool def)
{
        size_t start = state.code.count;

        switch (target->type) {
        case EXPRESSION_RESOURCE_BINDING:
                emit_instr(INSTR_PUSH_DROP);
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_TAG_PATTERN:
                emit_tgt(target->symbol, state.fscope, def);
                break;
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                emit_expression(target->object);
                emit_instr(INSTR_TARGET_MEMBER);
                emit_string(target->member_name);
                emit_ulong(strhash(target->member_name));
                break;
        case EXPRESSION_SUBSCRIPT:
                emit_expression(target->container);
                emit_expression(target->subscript);
                emit_instr(INSTR_TARGET_SUBSCRIPT);
                break;
        default:
                fail("oh no!");
        }

        if (KEEP_LOCATION(target))
                add_location(target, start, state.code.count);
}

static void
emit_dict_compr2(struct expression const *e)
{
        begin_loop(false, true);

        offset_vector successes_save = state.match_successes;
        offset_vector fails_save = state.match_fails;
        vec_init(state.match_successes);
        vec_init(state.match_fails);

        emit_instr(INSTR_SAVE_STACK_POS);
        emit_instr(INSTR_DICT);

        emit_instr(INSTR_PUSH_INDEX);
        if (e->dcompr.pattern->type == EXPRESSION_LIST) {
                emit_int((int)e->dcompr.pattern->es.count);
        } else {
                emit_int(1);
        }

        emit_expression(e->dcompr.iter);

        size_t start = state.code.count;
        emit_instr(INSTR_SAVE_STACK_POS);
        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_instr(INSTR_GET_NEXT);
        emit_instr(INSTR_READ_INDEX);

        add_location(e, start, state.code.count);

        size_t match, done;
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        emit_instr(INSTR_FIX_TO);
        emit_int((int)e->dcompr.pattern->es.count);

        for (int i = 0; i < e->dcompr.pattern->es.count; ++i) {
                emit_instr(INSTR_SAVE_STACK_POS);
                emit_try_match(e->dcompr.pattern->es.items[i]);
                emit_instr(INSTR_RESTORE_STACK_POS);
                emit_instr(INSTR_POP);
        }

        size_t cond_fail = 0;
        if (e->dcompr.cond != NULL) {
                emit_expression(e->dcompr.cond);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, cond_fail);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, match);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);
        if (e->dcompr.cond != NULL)
                PATCH_JUMP(cond_fail);
        emit_instr(INSTR_RESTORE_STACK_POS);
        JUMP(start);

        PATCH_JUMP(match);
        emit_instr(INSTR_RESTORE_STACK_POS);

        for (int i = e->elements.count - 1; i >= 0; --i) {
                emit_expression(e->keys.items[i]);
                if (e->values.items[i] != NULL)
                        emit_expression(e->values.items[i]);
                else
                        emit_instr(INSTR_NIL);
        }

        emit_instr(INSTR_DICT_COMPR);
        emit_int((int)e->elements.count);
        JUMP(start);
        PATCH_JUMP(done);
        emit_instr(INSTR_RESTORE_STACK_POS);
        patch_loop_jumps(start, state.code.count);
        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        end_loop();
}

static void
emit_array_compr2(struct expression const *e)
{
        begin_loop(false, true);

        offset_vector successes_save = state.match_successes;
        offset_vector fails_save = state.match_fails;
        vec_init(state.match_successes);
        vec_init(state.match_fails);

        emit_instr(INSTR_SAVE_STACK_POS);
        emit_instr(INSTR_ARRAY);

        emit_instr(INSTR_PUSH_INDEX);
        if (e->compr.pattern->type == EXPRESSION_LIST) {
                emit_int((int)e->compr.pattern->es.count);
        } else {
                emit_int(1);
        }

        emit_expression(e->compr.iter);

        size_t start = state.code.count;
        emit_instr(INSTR_SAVE_STACK_POS);
        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_instr(INSTR_GET_NEXT);
        emit_instr(INSTR_READ_INDEX);

        size_t match, done;
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        add_location(e, start, state.code.count);

        emit_instr(INSTR_FIX_TO);
        emit_int((int)e->compr.pattern->es.count);

        for (int i = 0; i < e->compr.pattern->es.count; ++i) {
                emit_instr(INSTR_SAVE_STACK_POS);
                emit_try_match(e->compr.pattern->es.items[i]);
                emit_instr(INSTR_RESTORE_STACK_POS);
                emit_instr(INSTR_POP);
        }

        size_t cond_fail = 0;
        if (e->compr.cond != NULL) {
                emit_expression(e->compr.cond);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, cond_fail);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, match);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);
        if (e->compr.cond != NULL)
                PATCH_JUMP(cond_fail);
        emit_instr(INSTR_RESTORE_STACK_POS);
        JUMP(start);

        PATCH_JUMP(match);
        emit_instr(INSTR_RESTORE_STACK_POS);

        emit_instr(INSTR_SAVE_STACK_POS);

        for (int i = e->elements.count - 1; i >= 0; --i) {
                if (e->aconds.items[i] != NULL) {
                        emit_expression(e->aconds.items[i]);
                        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t skip);
                        emit_expression(e->elements.items[i]);
                        PATCH_JUMP(skip);
                } else {
                        emit_expression(e->elements.items[i]);
                }
        }

        emit_instr(INSTR_ARRAY_COMPR);
        JUMP(start);
        PATCH_JUMP(done);
        emit_instr(INSTR_RESTORE_STACK_POS);
        patch_loop_jumps(start, state.code.count);
        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        end_loop();
}

static void
emit_spread(struct expression const *e, bool nils)
{
        emit_instr(INSTR_PUSH_INDEX);
        emit_int(1);

        if (e != NULL) {
                emit_expression(e);
        } else {
                emit_instr(INSTR_SWAP);
        }

        size_t start = state.code.count;
        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_instr(INSTR_GET_NEXT);
        emit_instr(INSTR_READ_INDEX);

        size_t done;
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        emit_instr(INSTR_FIX_TO);
        emit_int(1);

        emit_instr(INSTR_SWAP);
        emit_instr(INSTR_POP);

        emit_instr(INSTR_REVERSE);
        emit_int(3);

        if (nils) {
                emit_instr(INSTR_NIL);
                emit_instr(INSTR_REVERSE);
                emit_int(3);
        } else {
                emit_instr(INSTR_SWAP);
        }

        JUMP(start);

        PATCH_JUMP(done);

        emit_instr(INSTR_FIX_TO);
        emit_int(1);

        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);
}

static void
emit_conditional(struct expression const *e)
{
        emit_expression(e->cond);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t otherwise);
        emit_expression(e->then);
        PLACEHOLDER_JUMP(INSTR_JUMP, size_t end);
        PATCH_JUMP(otherwise);
        emit_expression(e->otherwise);
        PATCH_JUMP(end);
}

static void
emit_for_each2(struct statement const *s, bool want_result)
{
        begin_loop(want_result, true);

        offset_vector successes_save = state.match_successes;
        offset_vector fails_save = state.match_fails;
        vec_init(state.match_successes);
        vec_init(state.match_fails);

        emit_instr(INSTR_PUSH_INDEX);
        emit_int((int)s->each.target->es.count);

        emit_expression(s->each.array);

        size_t start = state.code.count;
        emit_instr(INSTR_SAVE_STACK_POS);
        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_instr(INSTR_GET_NEXT);
        emit_instr(INSTR_READ_INDEX);

#ifndef TY_ENABLE_PROFILING
        add_location(s->each.array, start, state.code.count);
#endif

        size_t match, done;
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        emit_instr(INSTR_FIX_TO);
        emit_int((int)s->each.target->es.count);

        if (s->each.target->has_resources) {
                emit_instr(INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        for (int i = 0; i < s->each.target->es.count; ++i) {
                emit_instr(INSTR_SAVE_STACK_POS);
                emit_try_match(s->each.target->es.items[i]);
                emit_instr(INSTR_RESTORE_STACK_POS);
                emit_instr(INSTR_POP);
        }

        size_t should_stop = 0;
        if (s->each.stop != NULL) {
                emit_expression(s->each.stop);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, should_stop);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, match);

        patch_jumps_to(&state.match_fails, state.code.count);

        // FIXME: are these useless?
        emit_instr(INSTR_RESTORE_STACK_POS);
        emit_instr(INSTR_RESTORE_STACK_POS);

        // Element doesn't match the for loop pattern
        add_location(s->each.target, state.code.count, state.code.count + 1);
        emit_instr(INSTR_BAD_MATCH);

        PATCH_JUMP(match);

        emit_instr(INSTR_RESTORE_STACK_POS);

        if (s->each.cond != NULL) {
                emit_expression(s->each.cond);
                JUMP_IF_NOT(start);
        }

        emit_statement(s->each.body, false);

        if (s->each.target->has_resources) {
                emit_instr(INSTR_DROP);
                state.resources -= 1;
        }

        JUMP(start);

        if (s->each.stop != NULL)
                PATCH_JUMP(should_stop);

        PATCH_JUMP(done);

        emit_instr(INSTR_RESTORE_STACK_POS);
        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);

        if (want_result)
                emit_instr(INSTR_NIL);

        patch_loop_jumps(start, state.code.count);

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        end_loop();
}

static bool
check_multi(struct expression *target, struct expression const *e, int *n)
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
emit_assignment2(struct expression *target, bool maybe, bool def)
{
        char instr = maybe ? INSTR_MAYBE_ASSIGN : INSTR_ASSIGN;

        size_t start = state.code.count;

        bool after = false;

        switch (target->type) {
        case EXPRESSION_ARRAY:
                for (int i = 0; i < target->elements.count; ++i) {
                        if (target->elements.items[i]->type == EXPRESSION_MATCH_REST) {
                                if (after) {
                                        state.start = target->elements.items[i]->start;
                                        state.end = target->elements.items[i]->end;
                                        fail("array pattern cannot contain multiple gather elements");
                                } else {
                                        after = true;
                                }
                                emit_target(target->elements.items[i], def);
                                emit_instr(INSTR_ARRAY_REST);
                                emit_int(i);
                                emit_int(target->elements.count - i - 1);
                                emit_int(sizeof (int) + 1);
                                emit_instr(INSTR_JUMP);
                                emit_int(1);
                                emit_instr(INSTR_BAD_MATCH);
                        } else {
                                emit_instr(INSTR_PUSH_ARRAY_ELEM);
                                if (after) {
                                        if (target->optional.items[i]) {
                                                state.start = target->elements.items[i]->start;
                                                state.end = target->elements.items[i]->end;
                                                fail("optional element cannot come after a gather element in array pattern");
                                        }
                                        emit_int(i - target->elements.count);
                                } else {
                                        emit_int(i);
                                }
                                emit_boolean(!target->optional.items[i]);
                                emit_assignment2(target->elements.items[i], maybe, def);
                                emit_instr(INSTR_POP);
                        }
                }
                break;
        case EXPRESSION_DICT:
                for (int i = 0; i < target->keys.count; ++i) {
                        emit_instr(INSTR_DUP);
                        emit_expression(target->keys.items[i]);
                        emit_instr(INSTR_SUBSCRIPT);
                        emit_assignment2(target->values.items[i], maybe, def);
                        emit_instr(INSTR_POP);
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_instr(INSTR_UNTAG_OR_DIE);
                emit_int(target->symbol->tag);
                emit_assignment2(target->tagged, maybe, def);
                break;
        case EXPRESSION_TAG_PATTERN:
                emit_target(target, def);
                emit_instr(INSTR_STEAL_TAG);
                emit_assignment2(target->tagged, maybe, def);
                break;
        case EXPRESSION_VIEW_PATTERN:
                emit_instr(INSTR_DUP);
                emit_expression(target->left);
                emit_instr(INSTR_CALL);
                emit_int(1);
                emit_int(0);
                add_location(target->left, start, state.code.count);
                emit_assignment2(target->right, maybe, def);
                emit_instr(INSTR_POP);
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                emit_instr(INSTR_DUP);
                emit_expression(target->left);
                emit_instr(INSTR_CALL);
                emit_int(1);
                emit_int(0);
                add_location(target->left, start, state.code.count);
                emit_instr(INSTR_THROW_IF_NIL);
                add_location(target, state.code.count - 1, state.code.count);
                emit_assignment2(target->right, maybe, def);
                emit_instr(INSTR_POP);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_instr(INSTR_THROW_IF_NIL);
                emit_target(target, def);
                emit_instr(instr);
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < target->es.count; ++i) {
                        if (target->es.items[i]->type == EXPRESSION_MATCH_REST) {
                                if (has_any_names(target)) {
                                        emit_record_rest(target, i, true);
                                } else {
                                        // FIXME: should we handle elements after the match-rest?
                                        emit_target(target->es.items[i], def);
                                        emit_instr(INSTR_TUPLE_REST);
                                        emit_int(i);
                                        emit_int(sizeof (int) + 1);
                                        emit_instr(INSTR_JUMP);
                                        emit_int(1);
                                        emit_instr(INSTR_BAD_MATCH);
                                }
                        } else if (target->names.items[i] != NULL) {
                                emit_instr(INSTR_PUSH_TUPLE_MEMBER);
                                emit_boolean(target->required.items[i]);
                                emit_string(target->names.items[i]);
                                emit_assignment2(target->es.items[i], maybe, def);
                                emit_instr(INSTR_POP);
                        } else {
                                emit_instr(INSTR_PUSH_TUPLE_ELEM);
                                emit_int(i);
                                emit_assignment2(target->es.items[i], maybe, def);
                                emit_instr(INSTR_POP);
                        }
                }
                break;
        default:
                emit_target(target, def);
                emit_instr(instr);
                if (target->type == EXPRESSION_IDENTIFIER && target->constraint != NULL && CheckConstraints) {
                        size_t start = state.code.count;
                        emit_instr(INSTR_DUP);
                        emit_expression(target->constraint);
                        emit_instr(INSTR_CHECK_MATCH);
                        PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t good);
                        emit_instr(INSTR_BAD_ASSIGN);
                        emit_string(target->identifier);
                        PATCH_JUMP(good);
                        add_location(target->constraint, start, state.code.count);
                }

#ifndef TY_ENABLE_PROFILING
                // Don't need location info, can't fail here
                return;
#endif
        }

        add_location(target, start, state.code.count);
}

static void
emit_assignment(struct expression *target, struct expression const *e, bool maybe, bool def)
{
        if (target->has_resources) {
                emit_instr(INSTR_PUSH_DROP_GROUP);
                state.resources += 1;
        }

        if (target->type == EXPRESSION_LIST) {
                emit_list(e);
                emit_instr(INSTR_FIX_TO);
                emit_int(target->es.count);
                for (int i = 0; i < target->es.count; ++i) {
                        emit_assignment2(target->es.items[i], maybe, def);
                        emit_instr(INSTR_POP);
                }
                emit_instr(INSTR_POP);
                emit_instr(INSTR_NIL);
        } else {
                emit_expression(e);
                emit_assignment2(target, maybe, def);
        }
}

static void
emit_non_nil_expr(struct expression const *e, bool none)
{
        emit_expression(e);
        emit_instr(INSTR_DUP);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NIL, size_t skip);
        PLACEHOLDER_JUMP(INSTR_JUMP, size_t good);
        PATCH_JUMP(skip);
        emit_instr(INSTR_POP);
        if (none) {
                emit_instr(INSTR_NONE);
        }
        PATCH_JUMP(good);
}

static void
emit_expr(struct expression const *e, bool need_loc)
{
        state.start = e->start;
        state.end = e->end;

        size_t start = state.code.count;
        char const *method = NULL;

        TryState *try = get_try(0);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                emit_load(e->symbol, state.fscope);
                break;
        case EXPRESSION_IFDEF:
                emit_load(e->symbol, state.fscope);
                emit_instr(INSTR_TAG_PUSH);
                emit_int(TAG_SOME);
                break;
        case EXPRESSION_NONE:
                emit_instr(INSTR_TAG);
                emit_int(TAG_NONE);
                break;
        case EXPRESSION_VALUE:
                emit_instr(INSTR_VALUE);
                emit_symbol((uintptr_t)e->v);
                break;
        case EXPRESSION_MATCH:
                emit_match_expression(e);
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_expression(e->tagged);
                emit_instr(INSTR_TAG_PUSH);
                emit_int(e->symbol->tag);
                break;
        case EXPRESSION_DOT_DOT:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_RANGE);
                break;
        case EXPRESSION_DOT_DOT_DOT:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_INCRANGE);
                break;
        case EXPRESSION_EQ:
                emit_assignment(e->target, e->value, false, false);
                break;
        case EXPRESSION_MAYBE_EQ:
                emit_assignment(e->target, e->value, true, false);
                break;
        case EXPRESSION_INTEGER:
                emit_instr(INSTR_INTEGER);
                emit_integer(e->integer);
                break;
        case EXPRESSION_BOOLEAN:
                emit_instr(INSTR_BOOLEAN);
                emit_boolean(e->boolean);
                break;
        case EXPRESSION_REAL:
                emit_instr(INSTR_REAL);
                emit_float(e->real);
                break;
        case EXPRESSION_STRING:
                emit_instr(INSTR_STRING);
                emit_string(e->string);
                break;
        case EXPRESSION_SPECIAL_STRING:
                emit_special_string(e);
                break;
        case EXPRESSION_EVAL:
                emit_expression(e->operand);
                emit_instr(INSTR_EVAL);
                emit_symbol((uintptr_t)e->escope);
                break;
        case EXPRESSION_TAG:
                emit_instr(INSTR_TAG);
                emit_int(e->symbol->tag);
                break;
        case EXPRESSION_REGEX:
                emit_instr(INSTR_REGEX);
                emit_symbol((uintptr_t)e->regex);
                break;
        case EXPRESSION_ARRAY:
                emit_instr(INSTR_SAVE_STACK_POS);
                for (int i = 0; i < e->elements.count; ++i) {
                        if (e->aconds.items[i] != NULL) {
                                emit_expression(e->aconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t skip);
                                if (e->optional.items[i]) {
                                        emit_non_nil_expr(e->elements.items[i], false);
                                } else {
                                        emit_expression(e->elements.items[i]);
                                }
                                PATCH_JUMP(skip);
                        } else if (e->optional.items[i]) {
                                emit_non_nil_expr(e->elements.items[i], false);
                        } else {
                                emit_expression(e->elements.items[i]);
                        }
                }
                emit_instr(INSTR_ARRAY);
                break;
        case EXPRESSION_ARRAY_COMPR:
                emit_array_compr2(e);
                break;
        case EXPRESSION_DICT:
                emit_instr(INSTR_SAVE_STACK_POS);
                for (int i = e->keys.count - 1; i >= 0; --i) {
                        if (e->keys.items[i]->type == EXPRESSION_SPREAD) {
                                emit_spread(e->keys.items[i]->value, true);
                        } else {
                                emit_expression(e->keys.items[i]);
                                if (e->keys.items[i]->type == EXPRESSION_SPLAT) {
                                        emit_instr(INSTR_NONE);
                                } else if (e->values.items[i] == NULL) {
                                        emit_instr(INSTR_NIL);
                                } else {
                                        emit_expression(e->values.items[i]);
                                }
                        }
                }
                emit_instr(INSTR_DICT);
                if (e->dflt != NULL) {
                        emit_expression(e->dflt);
                        emit_instr(INSTR_DICT_DEFAULT);
                }
                break;
        case EXPRESSION_DICT_COMPR:
                emit_dict_compr2(e);
                break;
        case EXPRESSION_NIL:
                emit_instr(INSTR_NIL);
                break;
        case EXPRESSION_SELF:
                emit_instr(INSTR_NIL);
                break;
        case EXPRESSION_SPLAT:
                emit_expression(e->value);
                break;
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                emit_expression(e->object);
                if (e->maybe)
                        emit_instr(INSTR_TRY_MEMBER_ACCESS);
                else
                        emit_instr(INSTR_MEMBER_ACCESS);
                emit_string(e->member_name);
                emit_ulong(strhash(e->member_name));
                break;
        case EXPRESSION_SUBSCRIPT:
                emit_expression(e->container);
                emit_expression(e->subscript);
                emit_instr(INSTR_SUBSCRIPT);
                break;
        case EXPRESSION_STATEMENT:
                emit_statement(e->statement, true);
                break;
        case EXPRESSION_FUNCTION_CALL:
                if (is_variadic(e)) {
                        emit_instr(INSTR_SAVE_STACK_POS);
                }
                for (size_t i = 0; i < e->args.count; ++i) {
                        if (e->args.items[i] == NULL) {
                                continue;
                        } else if (e->fconds.items[i] != NULL) {
                                emit_expression(e->fconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t skip);
                                emit_expression(e->args.items[i]);
                                PATCH_JUMP(skip);
                        } else {
                                emit_expression(e->args.items[i]);
                        }
                }
                for (size_t i = 0; i < e->kwargs.count; ++i) {
                        emit_expression(e->kwargs.items[i]);
                }
                emit_expression(e->function);
                emit_instr(INSTR_CALL);
                if (is_variadic(e)) {
                        emit_int(-1);
                } else {
                        emit_int(e->args.count);
                }
                emit_int(e->kwargs.count);
                for (size_t i = e->kws.count; i > 0; --i) {
                        emit_string(e->kws.items[i - 1]);
                }
                break;
        case EXPRESSION_METHOD_CALL:
                if (is_variadic(e)) {
                        emit_instr(INSTR_SAVE_STACK_POS);
                }
                for (size_t i = 0; i < e->method_args.count; ++i) {
                        if (e->method_args.items[i] == NULL) {
                                continue;
                        } else if (e->mconds.items[i] != NULL) {
                                emit_expression(e->mconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t skip);
                                emit_expression(e->method_args.items[i]);
                                PATCH_JUMP(skip);
                        } else {
                                emit_expression(e->method_args.items[i]);
                        }
                }
                for (size_t i = 0; i < e->method_kwargs.count; ++i) {
                        emit_expression(e->method_kwargs.items[i]);
                }
                emit_expression(e->object);
                if (e->maybe)
                        emit_instr(INSTR_TRY_CALL_METHOD);
                else
                        emit_instr(INSTR_CALL_METHOD);
                if (is_variadic(e)) {
                        emit_int(-1);
                } else {
                        emit_int(e->method_args.count);
                }
                emit_string(e->method_name);
                emit_ulong(strhash(e->method_name));

                emit_int(e->method_kwargs.count);
                for (size_t i = e->method_kws.count; i > 0; --i) {
                        emit_string(e->method_kws.items[i - 1]);
                }
                break;
        case EXPRESSION_WITH:
                emit_with(e);
                break;
        case EXPRESSION_YIELD:
                emit_yield((struct expression const **)e->es.items, e->es.count, true);
                break;
        case EXPRESSION_THROW:
                if (try != NULL && try->finally) {
                        fail("invalid 'throw' statement (occurs in a finally block)");
                }
                emit_expression(e->throw);
                emit_instr(INSTR_THROW);
                break;
        case EXPRESSION_SPREAD:
                emit_spread(e->value, false);
                break;
        case EXPRESSION_USER_OP:
                emit_expression(e->left);
                size_t sc;
                if (e->sc != NULL) {
                        emit_instr(INSTR_DUP);
                        emit_expression(e->sc);
                        emit_instr(INSTR_CHECK_MATCH);
                        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, sc);
                }
                emit_expression(e->right);
                emit_instr(INSTR_SWAP);
                emit_instr(INSTR_CALL_METHOD);
                emit_int(1);
                emit_string(e->op_name);
                emit_ulong(strhash(e->op_name));
                emit_int(0);
                if (e->sc != NULL) {
                        PATCH_JUMP(sc);
                }
                break;
        case EXPRESSION_BIT_OR:
                if (method == NULL) method = "|";
        case EXPRESSION_BIT_AND:
                if (method == NULL) method = "&";
        case EXPRESSION_KW_OR:
                if (method == NULL) method = "__or__";
        case EXPRESSION_KW_AND:
                if (method == NULL) method = "__and__";
                emit_expression(e->right);
                emit_expression(e->left);
                emit_instr(INSTR_CALL_METHOD);
                emit_int(1);
                emit_string(method);
                emit_ulong(strhash(method));
                emit_int(0);
                break;
        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
                method = "contains?";
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_CALL_METHOD);
                emit_int(1);
                emit_string(method);
                emit_ulong(strhash(method));
                emit_int(0);
                if (e->type == EXPRESSION_NOT_IN) {
                        emit_instr(INSTR_NOT);
                }
                break;
        case EXPRESSION_GENERATOR:
                emit_function(e, -1);
                emit_instr(INSTR_CALL);
                emit_int(0);
                emit_int(0);
                break;
        case EXPRESSION_FUNCTION:
        case EXPRESSION_MULTI_FUNCTION:
                emit_function(e, -1);
                break;
        case EXPRESSION_PLUS:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_ADD);
                break;
        case EXPRESSION_MINUS:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_SUB);
                break;
        case EXPRESSION_STAR:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_MUL);
                break;
        case EXPRESSION_DIV:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_DIV);
                break;
        case EXPRESSION_PERCENT:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_MOD);
                break;
        case EXPRESSION_AND:
                emit_and(e->left, e->right);
                break;
        case EXPRESSION_OR:
                emit_or(e->left, e->right);
                break;
        case EXPRESSION_WTF:
                emit_coalesce(e->left, e->right);
                break;
        case EXPRESSION_CONDITIONAL:
                emit_conditional(e);
                break;
        case EXPRESSION_LT:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_LT);
                break;
        case EXPRESSION_LEQ:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_LEQ);
                break;
        case EXPRESSION_GT:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_GT);
                break;
        case EXPRESSION_GEQ:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_GEQ);
                break;
        case EXPRESSION_CMP:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_CMP);
                break;
        case EXPRESSION_DBL_EQ:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_EQ);
                break;
        case EXPRESSION_NOT_EQ:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_NEQ);
                break;
        case EXPRESSION_CHECK_MATCH:
                emit_expression(e->left);
                emit_expression(e->right);
                emit_instr(INSTR_CHECK_MATCH);
                break;
        case EXPRESSION_PREFIX_BANG:
                emit_expression(e->operand);
                emit_instr(INSTR_NOT);
                break;
        case EXPRESSION_PREFIX_HASH:
                emit_expression(e->operand);
                emit_instr(INSTR_COUNT);
                break;
        case EXPRESSION_PREFIX_QUESTION:
                emit_expression(e->operand);
                emit_instr(INSTR_QUESTION);
                break;
        case EXPRESSION_PREFIX_AT:
                emit_expression(e->operand);
                emit_instr(INSTR_GET_TAG);
                break;
        case EXPRESSION_PREFIX_MINUS:
                emit_expression(e->operand);
                emit_instr(INSTR_NEG);
                break;
        case EXPRESSION_PREFIX_INC:
                emit_target(e->operand, false);
                emit_instr(INSTR_PRE_INC);
                break;
        case EXPRESSION_PREFIX_DEC:
                emit_target(e->operand, false);
                emit_instr(INSTR_PRE_DEC);
                break;
        case EXPRESSION_POSTFIX_INC:
                emit_target(e->operand, false);
                emit_instr(INSTR_POST_INC);
                break;
        case EXPRESSION_POSTFIX_DEC:
                emit_target(e->operand, false);
                emit_instr(INSTR_POST_DEC);
                break;
        case EXPRESSION_PLUS_EQ:
                emit_expression(e->value);
                emit_target(e->target, false);
                emit_instr(INSTR_MUT_ADD);
                break;
        case EXPRESSION_STAR_EQ:
                emit_target(e->target, false);
                emit_expression(e->value);
                emit_instr(INSTR_MUT_MUL);
                break;
        case EXPRESSION_DIV_EQ:
                emit_target(e->target, false);
                emit_expression(e->value);
                emit_instr(INSTR_MUT_DIV);
                break;
        case EXPRESSION_MINUS_EQ:
                emit_target(e->target, false);
                emit_expression(e->value);
                emit_instr(INSTR_MUT_SUB);
                break;
        case EXPRESSION_TUPLE:
                emit_instr(INSTR_SAVE_STACK_POS);
                for (int i = 0; i < e->es.count; ++i) {
                        if (e->tconds.items[i] != NULL) {
                                emit_expression(e->tconds.items[i]);
                                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t skip);
                                if (!e->required.items[i]) {
                                        emit_non_nil_expr(e->es.items[i], true);
                                } else {
                                        emit_expression(e->es.items[i]);
                                }
                                PLACEHOLDER_JUMP(INSTR_JUMP, size_t good);
                                PATCH_JUMP(skip);
                                emit_instr(INSTR_NONE);
                                PATCH_JUMP(good);
                        } else if (!e->required.items[i]) {
                                emit_non_nil_expr(e->es.items[i], true);
                        } else if (e->es.items[i]->type == EXPRESSION_SPREAD) {
                                emit_expression(e->es.items[i]->value);
                        } else {
                                emit_expression(e->es.items[i]);
                        }
                }
                emit_instr(INSTR_TUPLE);
                for (int i = 0; i < e->names.count; ++i) {
                        if (e->names.items[i] != NULL) {
                                emit_string(e->names.items[i]);
                        } else {
                                VPush(state.code, 0);
                        }
                }
                break;
        case EXPRESSION_TEMPLATE:
                for (int i = e->template.exprs.count - 1; i >= 0; --i) {
                        emit_expression(e->template.exprs.items[i]);
                }
                emit_instr(INSTR_RENDER_TEMPLATE);
                emit_symbol((uintptr_t)e);
                break;
        default:
                fail("expression unexpected in this context: %s", ExpressionTypeName(e));
        }

        if (KEEP_LOCATION(e) || need_loc)
                add_location(e, start, state.code.count);
}

static void
emit_expression(struct expression const *e)
{
        emit_expr(e, false);
}

static bool
emit_statement(struct statement const *s, bool want_result)
{
        state.start = s->start;
        state.end = s->end;

        bool returns = false;

        int resources = state.resources;

#ifdef TY_ENABLE_PROFILING
        size_t start = state.code.count;
#endif

        LoopState *loop = get_loop(0);

        switch (s->type) {
        case STATEMENT_BLOCK:
        case STATEMENT_MULTI:
                for (int i = 0; !returns && i < s->statements.count; ++i) {
                        bool wr = want_result && (i + 1 == s->statements.count);
                        returns |= emit_statement(s->statements.items[i], wr);
                }
                if (s->statements.count > 0) {
                        want_result = false;
                }
                while (state.resources > resources) {
                        emit_instr(INSTR_DROP);
                        state.resources -= 1;
                }
                break;
        case STATEMENT_MATCH:
                returns |= emit_match_statement(s, want_result);
                want_result = false;
                break;
        case STATEMENT_FOR_LOOP:
                emit_for_loop(s, want_result);
                want_result = false;
                break;
        case STATEMENT_EACH_LOOP:
                emit_for_each2(s, want_result);
                want_result = false;
                break;
        case STATEMENT_WHILE_MATCH:
                emit_while_match(s, want_result);
                want_result = false;
                break;
        case STATEMENT_WHILE:
                emit_while(s, want_result);
                want_result = false;
                break;
        case STATEMENT_IF:
                returns |= (s->iff.neg ? emit_if_not(s, want_result) : emit_if(s, want_result));
                want_result = false;
                break;
        case STATEMENT_EXPRESSION:
                emit_expression(s->expression);
                if (!want_result) {
                        emit_instr(INSTR_POP);
                } else {
                        want_result = false;
                }
                break;
        case STATEMENT_DEFINITION:
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
                emit_assignment(s->target, s->value, false, true);
                emit_instr(INSTR_POP);
                break;
        case STATEMENT_TAG_DEFINITION:
                for (int i = 0; i < s->tag.methods.count; ++i) {
                        emit_function(s->tag.methods.items[i], CLASS_TAG);
                }

                emit_instr(INSTR_DEFINE_TAG);
                emit_int(s->tag.symbol);
                emit_int(s->tag.super == NULL ? -1 : s->tag.super->symbol->tag);
                emit_int(s->tag.methods.count);

                for (int i = s->tag.methods.count; i > 0; --i)
                        emit_string(s->tag.methods.items[i - 1]->name);

                break;
        case STATEMENT_CLASS_DEFINITION:
                for (int i = 0; i < s->class.setters.count; ++i) {
                        state.method = s->class.setters.items[i]->scope;
                        s->class.setters.items[i]->mtype = MT_SET;
                        emit_function(s->class.setters.items[i], s->class.symbol);
                }
                for (int i = 0; i < s->class.getters.count; ++i) {
                        state.method = s->class.getters.items[i]->scope;
                        s->class.getters.items[i]->mtype = MT_GET;
                        emit_function(s->class.getters.items[i], s->class.symbol);
                }
                for (int i = 0; i < s->class.methods.count; ++i) {
                        state.method = s->class.methods.items[i]->scope;
                        s->class.methods.items[i]->mtype = MT_INSTANCE;
                        emit_function(s->class.methods.items[i], s->class.symbol);
                }
                for (int i = 0; i < s->class.statics.count; ++i) {
                        state.method = s->class.statics.items[i]->scope;
                        s->class.statics.items[i]->mtype = MT_STATIC;
                        emit_function(s->class.statics.items[i], s->class.symbol);
                }

                emit_instr(INSTR_DEFINE_CLASS);
                emit_int(s->class.symbol);
                emit_int(s->class.statics.count);
                emit_int(s->class.methods.count);
                emit_int(s->class.getters.count);
                emit_int(s->class.setters.count);

                for (int i = s->class.statics.count; i > 0; --i)
                        emit_string(s->class.statics.items[i - 1]->name);

                for (int i = s->class.methods.count; i > 0; --i)
                        emit_string(s->class.methods.items[i - 1]->name);

                for (int i = s->class.getters.count; i > 0; --i)
                        emit_string(s->class.getters.items[i - 1]->name);

                for (int i = s->class.setters.count; i > 0; --i)
                        emit_string(s->class.setters.items[i - 1]->name);

                break;
        case STATEMENT_CLEANUP:
                want_result = false;
                emit_instr(INSTR_CLEANUP);
                break;
        case STATEMENT_TRY_CLEAN:
        case STATEMENT_TRY:
                returns |= emit_try(s, want_result);
                want_result = false;
                break;
        case STATEMENT_RETURN:
                returns |= emit_return(s);
                break;
        case STATEMENT_GENERATOR_RETURN:
                emit_yield((struct expression const **)s->returns.items, s->returns.count, false);
                emit_instr(INSTR_JUMP);
                VPush(state.generator_returns, state.code.count);
                emit_int(0);
                break;
        case STATEMENT_BREAK:
                loop = get_loop(s->depth - 1);

                if (loop == NULL) {
                        fail("invalid break statement (not inside a loop)");
                }

                for (int i = 0; i < s->depth; ++i) {
                        if (get_loop(i)->each) {
                                emit_instr(INSTR_POP);
                                emit_instr(INSTR_POP);
                        }
                }

                want_result = false;

                if (s->expression != NULL) {
                        emit_expression(s->expression);
                        if (!loop->wr)
                                emit_instr(INSTR_POP);
                } else if (loop->wr) {
                        emit_instr(INSTR_NIL);
                }

                for (int i = 0; get_try(i) != NULL && get_try(i)->t > loop->t; ++i) {
                        emit_instr(INSTR_FINALLY);
                }

                for (int i = loop->resources; i < state.resources; ++i) {
                        emit_instr(INSTR_DROP);
                }

                emit_instr(INSTR_JUMP);
                VPush(loop->breaks, state.code.count);
                emit_int(0);
                break;
        case STATEMENT_CONTINUE:
                loop = get_loop(s->depth - 1);

                if (loop == NULL)
                        fail("invalid continue statement (not inside a loop)");

                for (int i = 0; i < s->depth - 1; ++i) {
                        if (get_loop(i)->each) {
                                emit_instr(INSTR_POP);
                                emit_instr(INSTR_POP);
                        }
                }

                for (int i = 0; get_try(i) != NULL && get_try(i)->t > loop->t; ++i) {
                        emit_instr(INSTR_FINALLY);
                }

                for (int i = loop->resources; i < state.resources; ++i) {
                        emit_instr(INSTR_DROP);
                }

                emit_instr(INSTR_JUMP);
                VPush(loop->continues, state.code.count);
                emit_int(0);
                break;
        case STATEMENT_DROP:
                for (int i = 0; i < s->drop.count; ++i) {
                        emit_load(s->drop.items[i], state.fscope);
                        emit_instr(INSTR_TRY_CALL_METHOD);
                        emit_int(0);
                        emit_string("__drop__");
                        emit_ulong(strhash("__drop__"));
                        emit_int(0);
                        emit_instr(INSTR_POP);
                }
                break;
        case STATEMENT_DEFER:
                emit_expression(s->expression);
                emit_instr(INSTR_DEFER);
                break;
        case STATEMENT_NEXT:
                emit_expression(s->expression);
                emit_instr(INSTR_NEXT);
                break;
        }

        if (want_result)
                emit_instr(INSTR_NIL);

#ifdef TY_ENABLE_PROFILING
        if (s->type != STATEMENT_BLOCK && s->type != STATEMENT_MULTI && s->type != STATEMENT_EXPRESSION) {
                Expr *e = Allocate(sizeof *e);
                *e = (Expr){0};
                e->type = EXPRESSION_STATEMENT;
                e->start = s->start;
                e->end = s->end;
                e->filename = state.filename;
                e->statement = s;
                add_location(e, start, state.code.count);
        }
#endif

        return returns;
}

static void
emit_new_globals(void)
{
        for (size_t i = GlobalCount; i < global->owned.count; ++i) {
                struct symbol *s = global->owned.items[i];
                if (s->i < BuiltinCount)
                        continue;
                if (s->tag != -1) {
                        emit_instr(INSTR_TAG);
                        emit_int(s->tag);
                        emit_instr(INSTR_TARGET_GLOBAL);
                        emit_int(s->i);
                        emit_instr(INSTR_ASSIGN);
                        emit_instr(INSTR_POP);
                } else if (s->class != -1) {
                        emit_instr(INSTR_CLASS);
                        emit_int(s->class);
                        emit_instr(INSTR_TARGET_GLOBAL);
                        emit_int(s->i);
                        emit_instr(INSTR_ASSIGN);
                        emit_instr(INSTR_POP);
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

static struct scope *
get_module_scope(char const *name)
{
        for (int i = 0; i < modules.count; ++i)
                if (strcmp(name, modules.items[i].path) == 0)
                        return modules.items[i].scope;

        return NULL;
}

static void
declare_classes(struct statement *s)
{
        if (s->type == STATEMENT_MULTI) {
                for (int i = 0; i < s->statements.count; ++i) {
                        declare_classes(s->statements.items[i]);
                }
        } else if (s->type == STATEMENT_CLASS_DEFINITION) {
                if (scope_locally_defined(state.global, s->class.name)) {
                        fail(
                                "redeclaration of class %s%s%s%s%s",
                                TERM(1),
                                TERM(34),
                                s->class.name,
                                TERM(22),
                                TERM(39)
                        );
                }
                struct symbol *sym = addsymbol(state.global, s->class.name);
                sym->class = class_new(s->class.name, s->class.doc);
                sym->cnst = true;
                s->class.symbol = sym->class;

                if (s->class.pub) {
                        VPush(state.exports, s->class.name);
                }
        }
}

static void
compile(char const *source)
{
        struct statement **p = parse(source, state.filename);
        if (p == NULL) {
                Error = parse_error();
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
                        struct expression *multi = mkmulti(p[i]->target->identifier, false);
                        bool pub = p[i]->pub;

                        struct statement *def = Allocate(sizeof *def);
                        *def = (struct statement){0};
                        def->type = STATEMENT_FUNCTION_DEFINITION;
                        def->target = Allocate(sizeof *def->target);
                        *def->target = (struct expression) {
                                .type = EXPRESSION_IDENTIFIER,
                                .start = p[i]->target->start,
                                .end = p[i]->target->end,
                                .filename = state.filename,
                                .identifier = multi->name
                        };
                        def->value = multi;
                        def->pub = pub;

                        define_function(def);
                        symbolize_statement(state.global, def);

                        int m = 0;
                        do {
                                p[i + m]->pub = false;
                                p[i + m]->value->is_overload = true;
                                snprintf(buffer, sizeof buffer - 1, "%s#%d", multi->name, m + 1);
                                p[i + m]->target->identifier = p[i + m]->value->name = sclonea(buffer);
                                VPush(multi->functions, (struct expression *)p[i + m]);
                                define_function(p[i + m]);
                                symbolize_statement(state.global, p[i + m]);
                                m += 1;
                        } while (
                                p[i + m] != NULL &&
                                p[i + m]->type == STATEMENT_FUNCTION_DEFINITION &&
                                strcmp(multi->name, p[i + m]->target->identifier) == 0
                        );

                        VPush(multi_functions, def);
                }
        }

        for (size_t i = 0; p[i] != NULL; ++i) {
                symbolize_statement(state.global, p[i]);
        }

        for (int i = 0; i < state.exports.count; ++i) {
                struct symbol *s = scope_lookup(state.global, state.exports.items[i]);
                if (s == NULL)
                        fail("attempt to export non-existent variable '%s'", state.exports.items[i]);
                s->public = true;
        }

        emit_new_globals();

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
        for (int i = 0; p[i] != NULL; ++i) {
                if (p[i]->type == STATEMENT_FUNCTION_DEFINITION) {
                        for (int j = i - 1; j >= 0 && p[j]->type != STATEMENT_FUNCTION_DEFINITION
                                                 && p[j]->type != STATEMENT_IMPORT; --j) {
                                struct statement *s = p[j];
                                p[j] = p[j + 1];
                                p[j + 1] = s;
                        }
                }
        }

        for (int i = 0; i < multi_functions.count; ++i) {
                emit_statement(multi_functions.items[i], false);
        }

        for (int i = 0; p[i] != NULL; ++i) {
                emit_statement(p[i], false);
        }

        while (state.resources > 0) {
                emit_instr(INSTR_DROP);
                state.resources -= 1;
        }

        emit_instr(INSTR_HALT);

        /*
         * Add all of the location information from this compliation unit to the global list.
         */
        //struct location end = { 0 };
        //add_location(end, end, state);
        add_location_info();

        state.generator_returns.count = 0;
        state.tries.count = 0;
        state.loops.count = 0;
}

static struct scope *
load_module(char const *name, struct scope *scope)
{
        char *source = slurp_module(name);

        if (source == NULL) {
                return NULL;
        }

        /*
         * Save the current compiler state so we can restore it after compiling
         * this module.
         */
        struct state save = state;
        state = freshstate();
        state.filename = name;

        compile(source);

        struct scope *module_scope;
        char *code = state.code.items;

        if (scope != NULL) {
                scope_copy_public(scope, state.global, true);
                module_scope = scope;
        } else {
                module_scope = state.global;
                module_scope->external = true;

                struct module m = {
                        .path = name,
                        .code = code,
                        .scope = module_scope
                };

                VPushN(m.imports, state.imports.items, state.imports.count);

                VPush(modules, m);
        }

        state = save;

        // TODO: which makes more sense here?
        //emit_instr(INSTR_EXEC_CODE);
        //emit_symbol((uintptr_t) m.code);
        vm_exec(code);

        return module_scope;
}

bool
compiler_import_module(struct statement const *s)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return false;
        }

        import_module(s);

        RESTORE_JB;

        return true;
}

void
import_module(struct statement const *s)
{
        char const *name = s->import.module;
        char const *as = s->import.as;
        bool pub = s->import.pub;

        state.start = s->start;
        state.end = s->end;

        struct scope *module_scope = get_module_scope(name);

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
                        fail("there is already a module imported under the name '%s'", as);
                if (state.imports.items[i].scope == module_scope)
                        fail("the module '%s' has already been imported", name);
        }

        if (module_scope == NULL) {
                module_scope = load_module(name, NULL);
        }

        char const **identifiers = (char const **) s->import.identifiers.items;
        int n = s->import.identifiers.count;
        bool everything = n == 1 && strcmp(identifiers[0], "..") == 0;

        if (everything) {
                char const *id = scope_copy_public(state.global, module_scope, pub);
                if (id != NULL)
                        fail("module '%s' exports conflcting name '%s'", name, id);
        } else for (int i = 0; i < n; ++i) {
                struct symbol *s = scope_lookup(module_scope, identifiers[i]);
                if (s == NULL || !s->public)
                        fail("module '%s' does not export '%s'", name, identifiers[i]);
                if (scope_lookup(state.global, identifiers[i]) != NULL)
                        fail("module '%s' exports conflicting name '%s'", name, identifiers[i]);
                scope_insert(state.global, s)->public = pub;
        }

        VPush(state.imports, ((struct import){ .name = as, .scope = module_scope, .pub = pub }));

        import_vector pubs = get_module_public_imports(name);
}

char const *
compiler_error(void)
{
        return Error;
}

void
compiler_init(void)
{
        tags_init();

        state = freshstate();
        global = state.global;
}

void
compiler_load_builtin_modules(void)
{
        if (setjmp(jb) != 0) {
                fprintf(stderr, "Aborting, failed to load builtin modules: %s\n", compiler_error());
                exit(1);
        }

        load_module("ffi", get_module_scope("ffi"));
        load_module("os", get_module_scope("os"));
        load_module("ty", get_module_scope("ty"));
}

char *
compiler_load_prelude(void)
{
        if (setjmp(jb) != 0) {
                fprintf(stderr, "Aborting, failed to load prelude: %s\n", compiler_error());
                exit(1);
        }

        state.filename = "(prelude)";
        compile(slurp_module("prelude"));

        state.global = scope_new("(prelude)", state.global, false);

        state.imports.count = 0;

        return state.code.items;
}

int
gettag(char const *module, char const *name)
{
        struct symbol *sym = compiler_lookup(module, name);
        if (!(sym != NULL && sym->cnst && sym->tag != -1)) {
                fprintf(stderr, "failed to find tag %s%s%s\n", module ? module : "", module ? "." : "", name);
                exit(1);
        }
        return sym->tag;
}

struct symbol *
compiler_lookup(char const *module, char const *name)
{
        struct scope *mscope;

        if (module == NULL) {
                return scope_lookup(state.global, name);
        } else if (mscope = get_module_scope(module), mscope != NULL) {
                return scope_lookup(mscope, name);
        }

        return NULL;
}

/*
 * This name kind of sucks.
 */
void
compiler_introduce_symbol(char const *module, char const *name)
{
        struct scope *s;
        if (module == NULL) {
                s = global;
        } else {
                s = get_module_scope(module);

                if (s == NULL) {
                        ++builtin_modules;
                        s = scope_new(module, global, false);
                        VPush(modules, ((struct module){
                                .path = module,
                                .code = NULL,
                                .scope = s
                        }));
                }
        }

        struct symbol *sym = addsymbol(s, name);
        sym->public = true;
        LOG("%s got index %d", name, sym->i);

        BuiltinCount += 1;
}

void
compiler_introduce_tag(char const *module, char const *name)
{
        struct scope *s;
        if (module == NULL) {
                s = global;
        } else {
                s = get_module_scope(module);

                if (s == NULL) {
                        ++builtin_modules;
                        s = scope_new(module, NULL, false);
                        VPush(modules, ((struct module){
                                .path = module,
                                .code = NULL,
                                .scope = s
                        }));
                }
        }

        struct symbol *sym = addsymbol(s, name);
        sym->public = true;
        sym->cnst = true;
        sym->tag = tags_new(name);
        LOG("tag %s got index %d", name, sym->i);

        BuiltinCount += 1;
}

char *
compiler_compile_source(char const *source, char const *filename)
{
        vec_init(state.code);
        vec_init(state.selfs);
        vec_init(state.expression_locations);

        state.filename = filename;
        int symbol_count = scope_get_symbol();

        if (setjmp(jb) != 0) {
                scope_set_symbol(symbol_count);
                return NULL;
        }

        compile(source);

        char *code = state.code.items;

        vec_init(state.code);

        return code;
}

int
compiler_symbol_count(void)
{
        return scope_get_symbol();
}

struct location
compiler_find_definition(char const *file, int line, int col)
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
                return (struct location) {0};
        }

        for (int i = 0; i < locs->count; ++i) {
                if (locs->items[i].e->type == EXPRESSION_IDENTIFIER &&
                    locs->items[i].start.line == line &&
                    locs->items[i].start.col == col) {
                        return (struct location) {
                                .line = locs->items[i].e->symbol->loc.line,
                                .col = locs->items[i].e->symbol->loc.col,
                                .s = locs->items[i].e->symbol->file
                        };
                }
        }

        return (struct location) {0};
}

Expr const *
compiler_find_expr(char const *code)
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
compiler_get_completions(char const *mod, char const *prefix, char **out, int max)
{
        int n = 0;

        if (mod == NULL) {
                n += scope_get_completions(state.global, prefix, out + n, max - n);
                n += scope_get_completions(global, prefix, out + n, max - n);
                return n;
        }

        for (int i = 0; i < state.imports.count; ++i) {
                if (module_match(state.imports.items[i].name, mod)) {
                        return n + scope_get_completions(state.imports.items[i].scope, prefix, out + n, max - n);
                }
        }

        return 0;
}

bool
compiler_has_module(char const *name)
{
        for (int i = 0; i < state.imports.count; ++i) {
                if (module_match(state.imports.items[i].name, name)) {
                        return true;
                }
        }

        return false;
}

int
compiler_global_count(void)
{
        return (int)global->owned.count;
}

inline static char *
mkcstr(struct value const *v)
{
        char *s = Allocate(v->bytes + 1);

        memcpy(s, v->string, v->bytes);
        s[v->bytes] = '\0';

        return s;
}

uint32_t
source_register(void const *src)
{
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
source_lookup(uint32_t src)
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
                }
        }
}

struct value
tagged(int tag, struct value v, ...)
{
        va_list ap;

        va_start(ap, v);

        static vec(struct value) vs;
        vs.count = 0;

        struct value next = va_arg(ap, struct value);

        if (next.type == VALUE_NONE) {
                goto TagAndReturn;
        }

        VPush(vs, v);

        while (next.type != VALUE_NONE) {
                VPush(vs, next);
                next = va_arg(ap, struct value);
        }

        v = value_tuple(vs.count);
        for (int i = 0; i < vs.count; ++i) {
                v.items[i] = vs.items[i];
        }

TagAndReturn:
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(v.tags, tag);
        return v;
}

static struct value
typarts(condpart_vector const *parts)
{
        struct value v = ARRAY(value_array_new());

        for (int i = 0; i < parts->count; ++i) {
                struct condpart *part = parts->items[i];
                if (part->target != NULL) {
                        value_array_push(
                                v.array,
                                tagged(
                                        part->def ? TyLet : TyAssign,
                                        tyexpr(part->target),
                                        tyexpr(part->e),
                                        NONE
                                )
                        );
                } else {
                        value_array_push(v.array, tyexpr(part->e));
                }
        }

        return v;
}

inline static struct value
tyaitem(struct expression const *e, int i)
{
        return tagged(
                TyArrayItem,
                value_named_tuple(
                        "item", tyexpr(e->elements.items[i]),
                        "cond", (e->aconds.items[i] == NULL) ? NIL : tyexpr(e->aconds.items[i]),
                        "optional", BOOLEAN(e->optional.items[i]),
                        NULL
                ),
                NONE
        );
}

struct value
tyexpr(struct expression const *e)
{
        struct value v;

        if (e == NULL) {
                return NIL;
        }

        GC_OFF_COUNT += 1;

        fixup_module_access((Expr *)e, state.global);
        expedite_fun((Expr *)e, state.global);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                v = value_named_tuple(
                        "name", STRING_CLONE(e->identifier, strlen(e->identifier)),
                        "module", (e->module == NULL) ? NIL : STRING_CLONE(e->module, strlen(e->module)),
                        "constraint", (e->constraint == NULL) ? NIL : tyexpr(e->constraint),
                        NULL
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyId);
                break;
        case EXPRESSION_ALIAS_PATTERN:
                v = value_named_tuple(
                        "name",       STRING_CLONE(e->identifier, strlen(e->identifier)),
                        "pattern",    tyexpr(e->aliased),
                        "module",     (e->module == NULL) ? NIL : STRING_CLONE(e->module, strlen(e->module)),
                        "constraint", (e->constraint == NULL) ? NIL : tyexpr(e->constraint),
                        NULL
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyPatternAlias);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                v = value_named_tuple(
                        "name", STRING_CLONE(e->identifier, strlen(e->identifier)),
                        "module", (e->module == NULL) ? NIL : STRING_CLONE(e->module, strlen(e->module)),
                        NULL
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyNotNil);
                break;
        case EXPRESSION_RESOURCE_BINDING:
                v = tagged(
                        TyResource,
                        value_named_tuple(
                                "name", STRING_CLONE(e->identifier, strlen(e->identifier)),
                                "module", (e->module == NULL) ? NIL : STRING_CLONE(e->module, strlen(e->module)),
                                NULL
                        ),
                        NONE
                );
                break;
        case EXPRESSION_ARRAY:
                v = ARRAY(value_array_new());
                NOGC(v.array);
                for (int i = 0; i < e->elements.count; ++i) {
                        value_array_push(v.array, tyaitem(e, i));
                }
                OKGC(v.array);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyArray);
                break;
        case EXPRESSION_SPREAD:
                v = tyexpr(e->value);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(v.tags, TySpread);
                break;
        case EXPRESSION_SPLAT:
                v = tyexpr(e->value);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(v.tags, TySplat);
                break;
        case EXPRESSION_ARRAY_COMPR:
        {
                Array *avElems = value_array_new();

                for (int i = 0; i < e->elements.count; ++i) {
                        value_array_push(avElems, tyaitem(e, i));
                }

                v = value_named_tuple(
                        "items", ARRAY(avElems),
                        "pattern", tyexpr(e->compr.pattern),
                        "iter", tyexpr(e->compr.iter),
                        "cond", e->compr.cond == NULL ? NIL : tyexpr(e->compr.cond),
                        NULL
                );

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(v.tags, TyArrayCompr);

                break;
        }
        case EXPRESSION_EVAL:
                v = tagged(
                        TyEval,
                        tyexpr(e->operand),
                        NONE
                );
                break;
        case EXPRESSION_GENERATOR:
                v = tystmt(e->body);
                v.tags = tags_push(v.tags, TyGenerator);
                break;
        case EXPRESSION_FUNCTION:
        case EXPRESSION_IMPLICIT_FUNCTION:
        {
                Array *decorators = value_array_new();
                Array *params = value_array_new();

                int tag = (e->type == EXPRESSION_IMPLICIT_FUNCTION) ? TyImplicitFunc : TyFunc;

                v = tagged(
                        tag,
                        value_named_tuple(
                                "name", e->name != NULL ? STRING_CLONE(e->name, strlen(e->name)) : NIL,
                                "params", ARRAY(params),
                                "rt", e->return_type != NULL ? tyexpr(e->return_type) : NIL,
                                "body", tystmt(e->body),
                                "decorators", ARRAY(decorators),
                                NULL
                        ),
                        NONE
                );

                for (int i = 0; i < e->decorators.count; ++i) {
                        value_array_push(decorators, tyexpr(e->decorators.items[i]));
                }

                for (int i = 0; i < e->params.count; ++i) {
                        struct value name = STRING_CLONE(e->params.items[i], strlen(e->params.items[i]));
                        if (i == e->rest) {
                                value_array_push(
                                        params,
                                        tagged(TyGather, name, NONE)
                                );
                        } else if (i == e->ikwargs) {
                                value_array_push(
                                        params,
                                        tagged(TyKwargs, name, NONE)
                                );
                        } else {
                                struct value p = value_named_tuple(
                                        "name", name,
                                        "constraint", e->constraints.items[i] != NULL ? tyexpr(e->constraints.items[i]) : NIL,
                                        "default", e->dflts.items[i] != NULL ? tyexpr(e->dflts.items[i]) : NIL,
                                        NULL
                                );
                                value_array_push(params, tagged(TyParam, p, NONE));
                        }
                }

                break;
        }
        case EXPRESSION_TAG_PATTERN_CALL:
                try_symbolize_application(NULL, (Expr *)e);
        case EXPRESSION_TAG_PATTERN:
                v = value_tuple(2);
                v.items[0] = STRING_CLONE(e->identifier, strlen(e->identifier));
                v.items[1] = tyexpr(e->tagged);
                v = tagged(
                        TyTagPattern,
                        v,
                        NONE
                );
                break;
        case EXPRESSION_TUPLE:
                v = ARRAY(value_array_new());
                NOGC(v.array);
                for (int i = 0; i < e->es.count; ++i) {
                        Value name = (e->names.items[i] == NULL)
                                   ? NIL
                                   : STRING_CLONE(e->names.items[i], strlen(e->names.items[i]));
                        value_array_push(
                                v.array,
                                tagged(
                                        TyRecordEntry,
                                        value_named_tuple(
                                                "item", tyexpr(e->es.items[i]),
                                                "name", name,
                                                "cond", (e->tconds.items[i] == NULL) ? NIL : tyexpr(e->tconds.items[i]),
                                                "optional", BOOLEAN(!e->required.items[i]),
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                OKGC(v.array);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyRecord);
                break;
        case EXPRESSION_LIST:
                v = ARRAY(value_array_new());
                NOGC(v.array);
                for (int i = 0; i < e->es.count; ++i) {
                        value_array_push(v.array, tyexpr(e->es.items[i]));
                        continue;
                        value_array_push(
                                v.array,
                                tagged(
                                        TyRecordEntry,
                                        value_named_tuple(
                                                "item", tyexpr(e->es.items[i]),
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
                v.tags = tags_push(0, TyRecord);
                break;
        case EXPRESSION_YIELD:
                v = ARRAY(value_array_new());
                for (int i = 0; i < e->es.count; ++i) {
                        value_array_push(v.array, tyexpr(e->es.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyYield);
                break;
        case EXPRESSION_THROW:
                v = tagged(TyThrow, tyexpr(e->throw), NONE);
                break;
        case EXPRESSION_MATCH:
                v = value_tuple(2);
                v.items[0] = tyexpr(e->subject);
                v.items[1] = ARRAY(value_array_new());
                for (int i = 0; i < e->patterns.count; ++i) {
                        struct value case_ = value_tuple(2);
                        case_.items[0] = tyexpr(e->patterns.items[i]);
                        case_.items[1] = tyexpr(e->thens.items[i]);
                        value_array_push(
                                v.items[1].array,
                                case_
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyMatch);
                break;
        case EXPRESSION_DICT:
                v = tagged(
                        TyDict,
                        value_named_tuple(
                                "items", ARRAY(value_array_new()),
                                "default", e->dflt != NULL ? tyexpr(e->dflt) : NIL,
                                NULL
                        ),
                        NONE
                );
                NOGC(v.items[0].array);
                for (int i = 0; i < e->keys.count; ++i) {
                        value_array_push(
                                v.items[0].array,
                                tagged(
                                        TyDictItem,
                                        tyexpr(e->keys.items[i]),
                                        tyexpr(e->values.items[i]),
                                        NONE
                                )
                        );
                }
                OKGC(v.items[0].array);
                break;
        case EXPRESSION_FUNCTION_CALL:
                v = value_named_tuple(
                        "func", tyexpr(e->function),
                        "args", ARRAY(value_array_new()),
                        NULL
                );
                for (int i = 0; i < e->args.count; ++i) {
                        value_array_push(
                                v.items[1].array,
                                tagged(
                                        TyArg,
                                        value_named_tuple(
                                                "arg", tyexpr(e->args.items[i]),
                                                "cond", e->fconds.items[i] != NULL ? tyexpr(e->fconds.items[i]) : NIL,
                                                "name", NIL,
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                for (int i = 0; i < e->kws.count; ++i) {
                        value_array_push(
                                v.items[1].array,
                                tagged(
                                        TyArg,
                                        value_named_tuple(
                                                "arg", tyexpr(e->kwargs.items[i]),
                                                "cond", e->fkwconds.items[i] != NULL ? tyexpr(e->fkwconds.items[i]) : NIL,
                                                "name", STRING_CLONE(e->kws.items[i], strlen(e->kws.items[i])),
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyCall);
                break;
        case EXPRESSION_METHOD_CALL:
                v = value_named_tuple(
                        "object", tyexpr(e->function),
                        "method", STRING_CLONE(e->method_name, strlen(e->method_name)),
                        "args", ARRAY(value_array_new()),
                        NULL
                );
                for (int i = 0; i < e->method_args.count; ++i) {
                        value_array_push(
                                v.items[2].array,
                                tagged(
                                        TyArg,
                                        value_named_tuple(
                                                "arg", tyexpr(e->method_args.items[i]),
                                                "cond", e->mconds.items[i] != NULL ? tyexpr(e->mconds.items[i]) : NIL,
                                                "name", NIL,
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                for (int i = 0; i < e->method_kws.count; ++i) {
                        value_array_push(
                                v.items[2].array,
                                tagged(
                                        TyArg,
                                        value_named_tuple(
                                                "arg", tyexpr(e->method_kwargs.items[i]),
                                                // TODO conditional method kwargs
                                                "cond", NIL,
                                                "name", STRING_CLONE(e->method_kws.items[i], strlen(e->method_kws.items[i])),
                                                NULL
                                        ),
                                        NONE
                                )
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyMethodCall);
                break;
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                v = value_tuple(2);
                v.items[0] = tyexpr(e->object);
                v.items[1] = STRING_CLONE(e->member_name, strlen(e->member_name));
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyMemberAccess);
                break;
        case EXPRESSION_SUBSCRIPT:
                v = value_tuple(2);
                v.items[0] = tyexpr(e->container);
                v.items[1] = tyexpr(e->subscript);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TySubscript);
                break;
        case EXPRESSION_WITH:
                v = ARRAY(value_array_new());
                for (int i = 0; i < e->with.defs.count; ++i) {
                        value_array_push(v.array, tystmt(e->with.defs.items[i]));
                }
                v = tagged(
                        TyWith,
                        v,
                        tystmt(e->with.block->statements.items[1]->try.s),
                        NONE
                );
                break;
        case EXPRESSION_NIL:
                v = TAG(TyNil);
                break;
        case EXPRESSION_CONDITIONAL:
                v = tagged(
                        TyCond,
                        tyexpr(e->cond),
                        tyexpr(e->then),
                        tyexpr(e->otherwise),
                        NONE
                );
                break;
        case EXPRESSION_REGEX:
                v = tagged(TyRegex, REGEX(e->regex), NONE);
                break;
        case EXPRESSION_INTEGER:
                v = INTEGER(e->integer);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyInt);
                break;
        case EXPRESSION_REAL:
                v = REAL(e->real);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyFloat);
                break;
        case EXPRESSION_BOOLEAN:
                v = BOOLEAN(e->boolean);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyBool);
                break;
        case EXPRESSION_STRING:
                v = STRING_CLONE(e->string, strlen(e->string));
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyString);
                break;
        case EXPRESSION_SPECIAL_STRING:
                v = ARRAY(value_array_new());
                gc_push(&v);

                value_array_push(v.array, STRING_CLONE(e->strings.items[0], strlen(e->strings.items[0])));

                for (int i = 0; i < e->expressions.count; ++i) {
                        struct value expr = tyexpr(e->expressions.items[i]);
                        if (e->fmts.items[i] == NULL) {
                                value_array_push(v.array, expr);
                        } else {
                                struct value s = STRING_CLONE(e->fmts.items[i], strlen(e->fmts.items[i]));
                                value_array_push(v.array, PAIR(expr, s));
                        }
                        value_array_push(v.array, STRING_CLONE(e->strings.items[i + 1], strlen(e->strings.items[i + 1])));
                }

                gc_pop();

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TySpecialString);

                break;
        case EXPRESSION_USER_OP:
                v = tagged(
                        TyUserOp,
                        STRING_CLONE(e->op_name, strlen(e->op_name)),
                        tyexpr(e->left),
                        tyexpr(e->right),
                        NONE
                );
                break;
        case EXPRESSION_DOT_DOT:
                v = tagged(TyRange, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_DOT_DOT_DOT:
                v = tagged(TyIncRange, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_EQ:
                v = tagged(TyAssign, tyexpr(e->target), tyexpr(e->value), NONE);
                break;
        case EXPRESSION_GT:
                v = tagged(TyGT, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_GEQ:
                v = tagged(TyGEQ, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_LT:
                v = tagged(TyLT, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_LEQ:
                v = tagged(TyLEQ, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_CMP:
                v = tagged(TyCmp, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_WTF:
                v = tagged(TyWtf, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_PLUS:
                v = tagged(TyAdd, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_STAR:
                v = tagged(TyMul, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_MINUS:
                v = tagged(TySub, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_DIV:
                v = tagged(TyDiv, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_PERCENT:
                v = tagged(TyMod, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_DBL_EQ:
                v = tagged(TyEq, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_NOT_EQ:
                v = tagged(TyNotEq, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_CHECK_MATCH:
                v = tagged(TyMatches, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_IN:
                v = tagged(TyIn, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_NOT_IN:
                v = tagged(TyNotIn, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_OR:
                v = tagged(TyOr, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_AND:
                v = tagged(TyAnd, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_VIEW_PATTERN:
                v = tagged(TyView, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                v = tagged(TyNotNilView, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_PREFIX_HASH:
                v = tyexpr(e->operand);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(v.tags, TyCount);
                break;
        case EXPRESSION_PREFIX_BANG:
                v = tagged(TyNot, tyexpr(e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_MINUS:
                v = tagged(TyNeg, tyexpr(e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_QUESTION:
                v = tagged(TyQuestion, tyexpr(e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_INC:
                v = tagged(TyPreInc, tyexpr(e->operand), NONE);
                break;
        case EXPRESSION_POSTFIX_INC:
                v = tagged(TyPostInc, tyexpr(e->operand), NONE);
                break;
        case EXPRESSION_PREFIX_DEC:
                v = tagged(TyPreDec, tyexpr(e->operand), NONE);
                break;
        case EXPRESSION_POSTFIX_DEC:
                v = tagged(TyPostDec, tyexpr(e->operand), NONE);
                break;
        case EXPRESSION_DEFINED:
                v = tagged(
                        TyDefined,
                        value_named_tuple(
                                "name", STRING_CLONE(e->identifier, strlen(e->identifier)),
                                "module", (e->module == NULL) ? NIL : STRING_CLONE(e->module, strlen(e->module)),
                                NULL
                        ),
                        NONE
                );
                break;
        case EXPRESSION_IFDEF:
                v = tagged(
                        TyIfDef,
                        value_named_tuple(
                                "name", STRING_CLONE(e->identifier, strlen(e->identifier)),
                                "module", (e->module == NULL) ? NIL : STRING_CLONE(e->module, strlen(e->module)),
                                NULL
                        ),
                        NONE
                );
                break;
        case EXPRESSION_TEMPLATE_HOLE:
                v = *vm_get(e->integer);
                break;
        case EXPRESSION_TEMPLATE_VHOLE:
                v = tagged(TyValue, *vm_get(e->integer), NONE);
                break;
        case EXPRESSION_STATEMENT:
                v = tystmt(e->statement);
                break;
        case EXPRESSION_VALUE:
                v = tagged(TyValue, *e->v, NONE);
                break;
        default:
                v = tagged(TyExpr, PTR((void *)e), NONE);
        }

        GC_OFF_COUNT -= 1;

        v.src = source_register(e);

        return v;
}

struct value
tystmt(struct statement *s)
{
        struct value v;

        if (s == NULL) {
                return NIL;
        }

        ++GC_OFF_COUNT;

        switch (s->type) {
        case STATEMENT_DEFINITION:
                v = value_tuple(2);
                v.items[0] = tyexpr(s->target);
                v.items[1] = tyexpr(s->value);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyLet);
                break;
        case STATEMENT_CLASS_DEFINITION:
                v = value_named_tuple(
                        "name", STRING_CLONE(s->class.name, strlen(s->class.name)),
                        "super", s->class.super != NULL ? tyexpr(s->class.super) : NIL,
                        "methods", ARRAY(value_array_new()),
                        "getters", ARRAY(value_array_new()),
                        "setters", ARRAY(value_array_new()),
                        "statics", ARRAY(value_array_new()),
                        "fields",  ARRAY(value_array_new()),
                        NULL
                );
                for (int i = 0; i < s->class.methods.count; ++i) {
                        value_array_push(v.items[2].array, tyexpr(s->class.methods.items[i]));
                }
                for (int i = 0; i < s->class.getters.count; ++i) {
                        value_array_push(v.items[3].array, tyexpr(s->class.getters.items[i]));
                }
                for (int i = 0; i < s->class.setters.count; ++i) {
                        value_array_push(v.items[4].array, tyexpr(s->class.setters.items[i]));
                }
                for (int i = 0; i < s->class.statics.count; ++i) {
                        value_array_push(v.items[5].array, tyexpr(s->class.statics.items[i]));
                }
                for (int i = 0; i < s->class.fields.count; ++i) {
                        value_array_push(v.items[6].array, tyexpr(s->class.fields.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyClass);
                break;
        case STATEMENT_DEFER:
                v = tyexpr(s->expression);
                v.tags = tags_push(v.tags, TyDefer);
                break;
        case STATEMENT_RETURN:
                v = value_tuple(s->returns.count);
                for (int i = 0; i < s->returns.count; ++i) {
                        v.items[i] = tyexpr(s->returns.items[i]);
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyReturn);
                break;
        case STATEMENT_BREAK:
                v = tagged(
                        TyBreak,
                        value_named_tuple(
                                "value", (s->expression == NULL) ? NIL : tyexpr(s->expression),
                                "depth", INTEGER(s->depth),
                                NULL
                        ),
                        NONE
                );
                break;
        case STATEMENT_CONTINUE:
                v = tagged(
                        TyContinue,
                        INTEGER(s->depth),
                        NONE
                );
                break;
        case STATEMENT_MATCH:
                v = value_tuple(2);
                v.items[0] = tyexpr(s->match.e);
                v.items[1] = ARRAY(value_array_new());
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        struct value case_ = value_tuple(2);
                        case_.items[0] = tyexpr(s->match.patterns.items[i]);
                        case_.items[1] = tystmt(s->match.statements.items[i]);
                        value_array_push(
                                v.items[1].array,
                                case_
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyMatch);
                break;
        case STATEMENT_WHILE_MATCH:
                v = value_tuple(2);
                v.items[0] = tyexpr(s->match.e);
                v.items[1] = ARRAY(value_array_new());
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        struct value case_ = value_tuple(2);
                        case_.items[0] = tyexpr(s->match.patterns.items[i]);
                        case_.items[1] = tystmt(s->match.statements.items[i]);
                        value_array_push(
                                v.items[1].array,
                                case_
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyWhileMatch);
                break;
        case STATEMENT_EACH_LOOP:
        {
                Array *ps = value_array_new();

                v = value_named_tuple(
                        "pattern", ARRAY(ps),
                        "iter", tyexpr(s->each.array),
                        "expr", tystmt(s->each.body),
                        "cond", s->each.cond != NULL ? tyexpr(s->each.cond) : NIL,
                        "stop", s->each.stop != NULL ? tyexpr(s->each.stop) : NIL,
                        NULL
                );

                for (int i = 0; i < s->each.target->es.count; ++i) {
                       value_array_push(ps, tyexpr(s->each.target->es.items[i]));
                }

                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyEach);

                break;
        }
        case STATEMENT_FOR_LOOP:
                v = tagged(TyFor, value_tuple(4), NONE);
                v.items[0] = tystmt(s->for_loop.init);
                v.items[1] = tyexpr(s->for_loop.cond);
                v.items[2] = tyexpr(s->for_loop.next);
                v.items[3] = tystmt(s->for_loop.body);
                break;
        case STATEMENT_BLOCK:
                v = ARRAY(value_array_new());
                for (int i = 0; i < s->statements.count; ++i) {
                        value_array_push(v.array, tystmt(s->statements.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyBlock);
                break;
        case STATEMENT_MULTI:
                v = ARRAY(value_array_new());
                for (int i = 0; i < s->statements.count; ++i) {
                        value_array_push(v.array, tystmt(s->statements.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyMulti);
                break;
        case STATEMENT_WHILE:
                v = value_tuple(2);
                v.items[0] = typarts(&s->While.parts);
                v.items[1] = tystmt(s->While.block);
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyWhile);
                break;
        case STATEMENT_IF:
                v = value_tuple(3);
                v.items[0] = typarts(&s->iff.parts);
                v.items[1] = tystmt(s->iff.then);
                v.items[2] = s->iff.otherwise != NULL ? tystmt(s->iff.otherwise) : NIL;
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, s->iff.neg ? TyIfNot : TyIf);
                break;
        case STATEMENT_TRY:
        {
                Array *avCatches = value_array_new();

                for (int i = 0; i < s->try.handlers.count; ++i) {
                        Value catch = value_tuple(2);
                        catch.items[0] = tyexpr(s->try.patterns.items[i]);
                        catch.items[1] = tystmt(s->try.handlers.items[i]);
                        value_array_push(avCatches, catch);
                }

                v = tagged(
                        TyTry,
                        value_named_tuple(
                                "body", tystmt(s->try.s),
                                "catches", ARRAY(avCatches),
                                "always", (s->try.finally == NULL) ? NIL : tystmt(s->try.finally),
                                NULL
                        ),
                        NONE
                );

                break;
        }
        case STATEMENT_FUNCTION_DEFINITION:
                v = tyexpr(s->value);
                v.tags = tags_push(0, TyFuncDef);
                break;
        case STATEMENT_NULL:
                v = TAG(TyNull);
                break;
        case STATEMENT_EXPRESSION:
                v = tyexpr(s->expression);
                break;
        default:
                v = tagged(TyStmt, PTR((void *)s), NONE);
        }

        --GC_OFF_COUNT;

        v.src = source_register(s);

        return v;
}

condpart_vector
cparts(struct value *v)
{
        condpart_vector parts = {0};

        for (int i = 0; i < v->array->count; ++i) {
                struct value *part = &v->array->items[i];
                struct condpart *cp = Allocate(sizeof *cp);
                int tag = tags_first(part->tags);
                if (tag == TyLet) {
                        cp->def = true;
                        cp->target = cexpr(&part->items[0]);
                        cp->e = cexpr(&part->items[1]);
                } else if (tag == TyAssign) {
                        cp->def = false;
                        cp->target = cexpr(&part->items[0]);
                        cp->e = cexpr(&part->items[1]);
                } else {
                        cp->def = false;
                        cp->target = NULL;
                        cp->e = cexpr(part);
                }
                VPush(parts, cp);
        }

        return parts;
}

struct statement *
cstmt(struct value *v)
{
        Stmt *s = Allocate(sizeof *s);
        Stmt *src = source_lookup(v->src);

        *s = (Stmt){0};
        s->arena = GetArenaAlloc();

        if (src == NULL && wrapped_type(v) == VALUE_TUPLE) {
                Value *src_val = tuple_get(v, "src");
                if (src_val != NULL) {
                        src = source_lookup(src_val->src);
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

        int tag = tags_first(v->tags);

        switch (tag) {
        case TyStmt:
                return v->ptr;
        case TyLet:
        {
                struct value *pub = tuple_get(v, "public");
                s->type = STATEMENT_DEFINITION;
                s->pub = pub != NULL && value_truthy(pub);
                s->target = cexpr(&v->items[0]);
                s->value = cexpr(&v->items[1]);
                break;
        }
        case TyFuncDef:
        {
                struct value f = *v;
                f.tags = tags_push(0, TyFunc);
                s->type = STATEMENT_FUNCTION_DEFINITION;
                s->value = cexpr(&f);
                s->doc = NULL;
                s->target = Allocate(sizeof *s->target);
                *s->target = (struct expression){0};
                s->target->type = EXPRESSION_IDENTIFIER;
                s->target->identifier = mkcstr(tuple_get(v, "name"));
                s->target->module = NULL;
                s->target->constraint = NULL;
                s->target->symbolized = false;
                break;
        }
        case TyClass:
        {
                s->type = STATEMENT_CLASS_DEFINITION;
                s->class.name = mkcstr(tuple_get(v, "name"));
                s->class.doc = NULL;
                struct value *super = tuple_get(v, "super");
                s->class.super = (super != NULL && super->type != VALUE_NIL) ? cexpr(super) : NULL;
                struct value *methods = tuple_get(v, "methods");
                struct value *getters = tuple_get(v, "getters");
                struct value *setters = tuple_get(v, "setters");
                struct value *statics = tuple_get(v, "statics");
                struct value *fields = tuple_get(v, "fields");
                vec_init(s->class.methods);
                vec_init(s->class.getters);
                vec_init(s->class.setters);
                vec_init(s->class.statics);
                vec_init(s->class.fields);
                if (methods != NULL) for (int i = 0; i < methods->array->count; ++i) {
                        VPush(s->class.methods, cexpr(&methods->array->items[i]));
                }
                if (getters != NULL) for (int i = 0; i < getters->array->count; ++i) {
                        VPush(s->class.getters, cexpr(&getters->array->items[i]));
                }
                if (setters != NULL) for (int i = 0; i < setters->array->count; ++i) {
                        VPush(s->class.setters, cexpr(&setters->array->items[i]));
                }
                if (statics != NULL) for (int i = 0; i < statics->array->count; ++i) {
                        VPush(s->class.statics, cexpr(&statics->array->items[i]));
                }
                if (fields != NULL) for (int i = 0; i < fields->array->count; ++i) {
                        VPush(s->class.fields, cexpr(&fields->array->items[i]));
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
                s->iff.parts = cparts(&v->items[0]);
                s->iff.then = cstmt(&v->items[1]);
                if (v->count > 2 && v->items[2].type != VALUE_NIL) {
                        s->iff.otherwise = cstmt(&v->items[2]);
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
                        fail("non-array `catches` in ty.Try construction: %s", value_show_color(v));
                }

                s->try.s = cstmt(vBody);
                s->try.finally = (vFinally == NULL || vFinally->type == VALUE_NIL) ? NULL : cstmt(vFinally);

                for (int i = 0; i < vCatches->array->count; ++i) {
                        Value *catch = &vCatches->array->items[i];
                        if (catch->type != VALUE_TUPLE || catch->count != 2) {
                                fail("invalid `catches` entry in ty.Try construction: %s", value_show_color(catch));
                        }
                        VPush(s->try.patterns, cexpr(&catch->items[0]));
                        VPush(s->try.handlers, cstmt(&catch->items[1]));
                }

                break;
        }
        case TyDefer:
                v->tags = tags_pop(v->tags);
                s->type = STATEMENT_DEFER;
                s->expression = cexpr(v);
                break;
        case TyMatch:
        {
                s->type = STATEMENT_MATCH;
                s->match.e = cexpr(&v->items[0]);
                vec_init(s->match.patterns);
                vec_init(s->match.statements);
                vec_init(s->match.conds);
                struct value *cases = &v->items[1];
                for (int i = 0; i < cases->array->count; ++i) {
                        struct value *_case = &cases->array->items[i];
                        VPush(s->match.patterns, cexpr(&_case->items[0]));
                        VPush(s->match.statements, cstmt(&_case->items[1]));
                        VPush(s->match.conds, NULL);
                }
                break;
        }
        case TyWhileMatch:
        {
                s->type = STATEMENT_WHILE_MATCH;
                s->match.e = cexpr(&v->items[0]);
                vec_init(s->match.patterns);
                vec_init(s->match.statements);
                vec_init(s->match.conds);
                struct value *cases = &v->items[1];
                for (int i = 0; i < cases->array->count; ++i) {
                        struct value *_case = &cases->array->items[i];
                        VPush(s->match.patterns, cexpr(&_case->items[0]));
                        VPush(s->match.statements, cstmt(&_case->items[1]));
                        VPush(s->match.conds, NULL);
                }
                break;
        }
        case TyWhile:
                s->type = STATEMENT_WHILE;
                s->While.parts = cparts(&v->items[0]);
                s->While.block = cstmt(&v->items[1]);
                break;
        case TyFor:
                s->type = STATEMENT_FOR_LOOP;
                s->for_loop.init = cstmt(&v->items[0]);
                s->for_loop.cond = cexpr(&v->items[1]);
                s->for_loop.next = cexpr(&v->items[2]);
                s->for_loop.body = cstmt(&v->items[3]);
                break;
        case TyEach:
        {
                s->type = STATEMENT_EACH_LOOP;
                s->each.target = Allocate(sizeof (struct expression));
                s->each.target->type = EXPRESSION_LIST;
                vec_init(s->each.target->es);

                Value *ps = tuple_get(v, "pattern");
                if (ps->type == VALUE_ARRAY) {
                        for (int i = 0; i < ps->array->count; ++i) {
                                VPush(s->each.target->es, cexpr(&ps->array->items[i]));
                        }
                } else {
                        VPush(s->each.target->es, cexpr(ps));
                }

                s->each.array = cexpr(tuple_get(v, "iter"));
                s->each.body = cstmt(tuple_get(v, "expr"));
                struct value *cond = tuple_get(v, "cond");
                s->each.cond = (cond != NULL && cond->type != VALUE_NIL) ? cexpr(cond) : NULL;
                struct value *stop = tuple_get(v, "stop");
                s->each.stop = (stop != NULL && stop->type != VALUE_NIL) ? cexpr(stop) : NULL;
                break;
        }
        case TyReturn:
        {
                s->type = STATEMENT_RETURN;
                vec_init(s->returns);
                if (wrapped_type(v) == VALUE_TUPLE) {
                        for (int i = 0; i < v->count; ++i) {
                                VPush(s->returns, cexpr(&v->items[i]));
                        }
                } else {
                        Value v_ = unwrap(v);
                        Expr *ret = cexpr(&v_);
                        if (ret->type == EXPRESSION_LIST) {
                                VPushN(s->returns, ret->es.items, ret->es.count);
                        } else {
                                VPush(s->returns, cexpr(v));
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
                        s->expression = (expr == NULL || expr->type == VALUE_NIL) ? NULL : cexpr(expr);
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
                        VPush(s->statements, cstmt(&v->array->items[i]));
                }
                break;
        case TyMulti:
                s->type = STATEMENT_MULTI;
                vec_init(s->statements);
                for (int i = 0; i < v->array->count; ++i) {
                        VPush(s->statements, cstmt(&v->array->items[i]));
                }
                break;
        case TyNull:
        Null:
                s->type = STATEMENT_NULL;
                break;
        default:
                s->type = STATEMENT_EXPRESSION;
                s->expression = cexpr(v);
                if (s->filename == NULL && s->expression->filename != NULL) {
                        s->filename = s->expression->filename;
                        s->start = s->expression->start;
                        s->end = s->expression->end;
                }
                break;
        }

        return s;
}

struct expression *
cexpr(struct value *v)
{
        if (v->type == VALUE_NIL) {
                return NULL;
        }

        Expr *e = Allocate(sizeof *e);
        Expr *src = source_lookup(v->src);

        *e = (struct expression){0};
        e->arena = GetArenaAlloc();

        if (src == NULL && wrapped_type(v) == VALUE_TUPLE) {
                Value *src_val = tuple_get(v, "src");
                if (src_val != NULL) {
                        src = source_lookup(src_val->src);
                }
        }

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
        }

        int tag = tags_first(v->tags);

        switch (tag) {
        case 0:
                e->type = EXPRESSION_LIST;
                if (v->type != VALUE_ARRAY) {
                        goto Bad;
                }
                for (int i = 0; i < v->array->count; ++i) {
                        VPush(e->es, cexpr(&v->array->items[i]));
                }
                break;
        case TyExpr:
                return v->ptr;
        case TyValue:
        {
                struct value *value = Allocate(sizeof *value);
                *value = *v;
                value->tags = tags_pop(value->tags);
                if (value->tags == 0) {
                        value->type &= ~VALUE_TAGGED;
                }
                e->type = EXPRESSION_VALUE;
                e->v = value;
                gc_immortalize(value);
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
                e->identifier = mkcstr(tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                Value *constraint = tuple_get(v, "constraint");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(mod) : NULL;
                e->constraint = (constraint != NULL && constraint->type != VALUE_NIL) ? cexpr(constraint) : NULL;

                if (e->module == NULL && strcmp(e->identifier, "__line__") == 0) {
                        e->start = state.mstart;
                        e->end = state.mend;
                }

                break;
        }
        case TyPatternAlias:
        {
                e->type = EXPRESSION_ALIAS_PATTERN;
                e->identifier = mkcstr(tuple_get(v, "name"));
                Value *mod = tuple_get(v, "module");
                Value *constraint = tuple_get(v, "constraint");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(mod) : NULL;
                e->constraint = (constraint != NULL && constraint->type != VALUE_NIL) ? cexpr(constraint) : NULL;
                e->aliased = cexpr(tuple_get(v, "pattern"));
                break;
        }
        case TyNotNil:
        {
                e->type = EXPRESSION_MATCH_NOT_NIL;
                e->identifier = mkcstr(tuple_get(v, "name"));
                struct value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(mod) : NULL;
                break;
        }
        case TyResource:
        {
                e->type = EXPRESSION_RESOURCE_BINDING;
                e->identifier = mkcstr(tuple_get(v, "name"));
                struct value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(mod) : NULL;
                break;
        }
        case TySpread:
        {
                struct value v_ = *v;
                v_.tags = tags_pop(v_.tags);
                e->type = EXPRESSION_SPREAD;
                e->value = cexpr(&v_);
                break;
        }
        case TySplat:
        {
                struct value v_ = *v;
                v_.tags = tags_pop(v_.tags);
                e->type = EXPRESSION_SPLAT;
                e->value = cexpr(&v_);
                break;
        }
        case TyString:
                e->type = EXPRESSION_STRING;
                e->string = mkcstr(v);
                break;
        case TySpecialString:
        {
                e->type = EXPRESSION_SPECIAL_STRING;
                vec_init(e->strings);
                vec_init(e->expressions);
                vec_init(e->fmts);
                for (int i = 0; i < v->array->count; ++i) {
                        struct value *x = &v->array->items[i];
                        if (x->type == VALUE_STRING) {
                                VPush(e->strings, mkcstr(x));
                        } else if (x->type == VALUE_TUPLE) {
                                VPush(e->expressions, cexpr(&x->items[0]));
                                VPush(e->fmts, mkcstr(&x->items[1]));
                        } else {
                                VPush(e->expressions, cexpr(x));
                                VPush(e->fmts, NULL);
                        }
                }
                if (v->array->count == 0 || vec_last(*v->array)->type != VALUE_STRING) {
                        VPush(e->strings, "");
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
                        struct value *entry = &v->array->items[i];
                        struct value *optional = tuple_get(entry, "optional");
                        struct value *cond = tuple_get(entry, "cond");
                        VPush(e->elements, cexpr(tuple_get(entry, "item")));
                        VPush(e->optional, optional != NULL ? optional->boolean : false);
                        VPush(e->aconds, (cond != NULL && cond->type != VALUE_NIL) ? cexpr(cond) : NULL);
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
                        struct value *entry = &v->array->items[i];
                        struct value *item = tuple_get(entry, "item");
                        struct value *name = tuple_get(entry, "name");
                        struct value *optional = tuple_get(entry, "optional");
                        struct value *cond = tuple_get(entry, "cond");
                        VPush(e->es, cexpr(item));
                        VPush(e->names, name != NULL && name->type != VALUE_NIL ? mkcstr(name) : NULL);
                        VPush(e->required, optional != NULL ? !optional->boolean : true);
                        VPush(e->tconds, cond != NULL && cond->type != VALUE_NIL ? cexpr(cond) : NULL);
                }

                break;
        }
        case TyDict:
        {
                e->type = EXPRESSION_DICT;
                e->dtmp = NULL;
                vec_init(e->keys);
                vec_init(e->values);

                struct value *items = tuple_get(v, "items");
                struct value *dflt = tuple_get(v, "default");

                e->dflt = (dflt != NULL && dflt->type != VALUE_NIL) ? cexpr(dflt) : NULL;

                for (int i = 0; i < items->array->count; ++i) {
                        VPush(e->keys, cexpr(&items->array->items[i].items[0]));
                        VPush(e->values, cexpr(&items->array->items[i].items[1]));
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

                struct value *func = tuple_get(v, "func");
                e->function = cexpr(func);

                struct value *args = tuple_get(v, "args");

                for (int i = 0; i < args->array->count; ++i) {
                        struct value *arg = &args->array->items[i];
                        struct value *name = tuple_get(arg, "name");
                        struct value *cond = tuple_get(arg, "cond");
                        if (cond != NULL && cond->type == VALUE_NIL) {
                                cond = NULL;
                        }
                        if (name == NULL || name->type == VALUE_NIL) {
                                VPush(e->args, cexpr(tuple_get(arg, "arg")));
                                VPush(e->fconds, cond != NULL ? cexpr(cond) : NULL);
                        } else {
                                VPush(e->kwargs, cexpr(tuple_get(arg, "arg")));
                                VPush(e->kws, mkcstr(name));
                                VPush(e->fkwconds, cond != NULL ? cexpr(cond) : NULL);
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

                struct value *maybe = tuple_get(v, "maybe");
                e->maybe = maybe != NULL && value_truthy(maybe);

                struct value *object = tuple_get(v, "object");
                e->object = cexpr(object);

                struct value *method = tuple_get(v, "method");
                e->method_name = mkcstr(method);

                struct value *args = tuple_get(v, "args");

                for (int i = 0; i < args->array->count; ++i) {
                        struct value *arg = &args->array->items[i];
                        struct value *name = tuple_get(arg, "name");
                        struct value *cond = tuple_get(arg, "cond");
                        if (cond != NULL && cond->type == VALUE_NIL) {
                                cond = NULL;
                        }
                        if (name == NULL || name->type == VALUE_NIL) {
                                VPush(e->method_args, cexpr(tuple_get(arg, "arg")));
                                VPush(e->mconds, cond != NULL ? cexpr(cond) : NULL);
                        } else {
                                VPush(e->method_kwargs, cexpr(tuple_get(arg, "arg")));
                                VPush(e->method_kws, mkcstr(name));
                        }
                }
                break;
        }
        case TyGenerator:
        {
                struct value v_ = *v;
                v_.tags = tags_pop(v_.tags);
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
                e->body = cstmt(&v_);
                break;
        }
        case TyFunc:
        case TyImplicitFunc:
        {
                e->type = tag == TyFunc ? EXPRESSION_FUNCTION : EXPRESSION_IMPLICIT_FUNCTION;
                e->ikwargs = -1;
                e->rest = -1;
                e->ftype = FT_NONE;
                struct value *name = tuple_get(v, "name");
                struct value *params = tuple_get(v, "params");
                struct value *rt = tuple_get(v, "rt");
                Value *decorators = tuple_get(v, "decorators");
                e->name = (name != NULL && name->type != VALUE_NIL) ? mkcstr(name) : NULL;
                e->doc = NULL;
                e->proto = NULL;
                e->return_type = (rt != NULL && rt->type != VALUE_NIL) ? cexpr(rt) : NULL;
                vec_init(e->params);
                vec_init(e->constraints);
                vec_init(e->dflts);
                vec_init(e->decorators);
                if (decorators != NULL && decorators->type != VALUE_NIL) {
                        for (int i = 0; i < decorators->array->count; ++i) {
                                VPush(e->decorators, cexpr(&decorators->array->items[i]));
                        }
                }
                for (int i = 0; i < params->array->count; ++i) {
                        struct value *p = &params->array->items[i];
                        switch (tags_first(p->tags)) {
                        case TyParam:
                        {
                                VPush(e->params, mkcstr(tuple_get(p, "name")));
                                struct value *c = tuple_get(p, "constraint");
                                struct value *d = tuple_get(p, "default");
                                VPush(e->constraints, (c != NULL && c->type != VALUE_NIL) ? cexpr(c) : NULL);
                                VPush(e->dflts, (d != NULL && d->type != VALUE_NIL) ? cexpr(d) : NULL);
                                break;
                        }
                        case TyGather:
                                VPush(e->params, mkcstr(p));
                                VPush(e->constraints, NULL);
                                VPush(e->dflts, NULL);
                                e->rest = i;
                                break;
                        case TyKwargs:
                                VPush(e->params, mkcstr(p));
                                VPush(e->constraints, NULL);
                                VPush(e->dflts, NULL);
                                e->ikwargs = i;
                                break;
                        }
                }
                e->body = cstmt(tuple_get(v, "body"));
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
                e->compr.pattern = cexpr(pattern);
                e->compr.iter = cexpr(iter);
                e->compr.cond = (cond == NULL || cond->type == VALUE_NIL) ? NULL : cexpr(cond);

                vec_init(e->elements);
                vec_init(e->aconds);
                vec_init(e->optional);

                for (int i = 0; i < items->array->count; ++i) {
                        struct value *entry = &items->array->items[i];
                        struct value *optional = tuple_get(entry, "optional");
                        struct value *cond = tuple_get(entry, "cond");
                        VPush(e->elements, cexpr(tuple_get(entry, "item")));
                        VPush(e->optional, optional != NULL ? optional->boolean : false);
                        VPush(e->aconds, (cond != NULL && cond->type != VALUE_NIL) ? cexpr(cond) : NULL);
                }

                break;
        }
        case TyMemberAccess:
                e->type = EXPRESSION_MEMBER_ACCESS;
                e->object = cexpr(&v->items[0]);
                e->member_name = mkcstr(&v->items[1]);
                break;
        case TySubscript:
                e->type = EXPRESSION_SUBSCRIPT;
                e->container = cexpr(&v->items[0]);
                e->subscript = cexpr(&v->items[1]);
                break;
        case TyEval:
        {
                struct value v_ = *v;
                v_.tags = tags_pop(v_.tags);
                e->type = EXPRESSION_EVAL;
                e->operand = cexpr(&v_);
                break;
        }
        case TyYield:
                e->type = EXPRESSION_YIELD;
                vec_init(e->es);
                if ((v->type & ~VALUE_TAGGED) == VALUE_ARRAY) {
                        for (int i = 0; i < v->array->count; ++i) {
                                VPush(e->es, cexpr(&v->array->items[i]));
                        }
                } else {
                        struct value v_ = *v;
                        v_.tags = tags_pop(v_.tags);
                        VPush(e->es, cexpr(&v_));
                }
                break;
        case TyThrow:
        {
                Value v_ = unwrap(v);
                e->type = EXPRESSION_THROW;
                e->throw = cexpr(&v_);
                break;
        }
        case TyWith:
        {
                struct value *lets = &v->items[0];
                statement_vector defs = {0};

                for (int i = 0; i < lets->array->count; ++i) {
                        VPush(defs, cstmt(&lets->array->items[i]));
                }

                make_with(e, defs, cstmt(&v->items[1]));

                break;
        }
        case TyCond:
                e->type = EXPRESSION_CONDITIONAL;
                e->cond = cexpr(&v->items[0]);
                e->then = cexpr(&v->items[1]);
                e->otherwise = cexpr(&v->items[2]);
                break;
        case TyBool:
                e->type = EXPRESSION_BOOLEAN;
                e->boolean = v->boolean;
                break;
        case TyAssign:
                e->type = EXPRESSION_EQ;
                e->target = cexpr(&v->items[0]);
                e->value = cexpr(&v->items[1]);
                break;
        case TyRange:
                e->type = EXPRESSION_DOT_DOT;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyIncRange:
                e->type = EXPRESSION_DOT_DOT_DOT;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyView:
                e->type = EXPRESSION_VIEW_PATTERN;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyNotNilView:
                e->type = EXPRESSION_NOT_NIL_VIEW_PATTERN;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyWtf:
                e->type = EXPRESSION_WTF;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyAdd:
                e->type = EXPRESSION_PLUS;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TySub:
                e->type = EXPRESSION_MINUS;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyMod:
                e->type = EXPRESSION_PERCENT;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyDiv:
                e->type = EXPRESSION_DIV;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyMul:
                e->type = EXPRESSION_STAR;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyEq:
                e->type = EXPRESSION_DBL_EQ;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyNotEq:
                e->type = EXPRESSION_NOT_EQ;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyGT:
                e->type = EXPRESSION_GT;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyGEQ:
                e->type = EXPRESSION_GEQ;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyLT:
                e->type = EXPRESSION_LT;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyLEQ:
                e->type = EXPRESSION_LEQ;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyCmp:
                e->type = EXPRESSION_CMP;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyMatches:
                e->type = EXPRESSION_CHECK_MATCH;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyIn:
                e->type = EXPRESSION_IN;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyNotIn:
                e->type = EXPRESSION_NOT_IN;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyOr:
                e->type = EXPRESSION_OR;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyAnd:
                e->type = EXPRESSION_AND;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
                break;
        case TyUserOp:
                e->type = EXPRESSION_USER_OP;
                e->op_name = mkcstr(&v->items[0]);
                e->left = cexpr(&v->items[1]);
                e->right = cexpr(&v->items[2]);
                break;
        case TyCount:
        {
                struct value v_ = *v;
                v_.tags = tags_pop(v_.tags);
                e->type = EXPRESSION_PREFIX_HASH;
                e->operand = cexpr(&v_);
                break;
        }
        case TyNot:
        {
                Value v_ = unwrap(v);
                e->type = EXPRESSION_PREFIX_BANG;
                e->operand = cexpr(&v_);
                break;
        }
        case TyNeg:
        {
                Value v_ = unwrap(v);
                e->type = EXPRESSION_PREFIX_MINUS;
                e->operand = cexpr(&v_);
                break;
        }
        case TyPreInc:
        {
                Value v_ = unwrap(v);
                e->type = EXPRESSION_PREFIX_INC;
                e->operand = cexpr(&v_);
                break;
        }
        case TyPostInc:
        {
                Value v_ = unwrap(v);
                e->type = EXPRESSION_POSTFIX_INC;
                e->operand = cexpr(&v_);
                break;
        }
        case TyPreDec:
        {
                Value v_ = unwrap(v);
                e->type = EXPRESSION_PREFIX_DEC;
                e->operand = cexpr(&v_);
                break;
        }
        case TyPostDec:
        {
                Value v_ = unwrap(v);
                e->type = EXPRESSION_POSTFIX_DEC;
                e->operand = cexpr(&v_);
                break;
        }
        case TyQuestion:
        {
                Value v_ = unwrap(v);
                e->type = EXPRESSION_PREFIX_QUESTION;
                e->operand = cexpr(&v_);
                break;
        }
        case TyTagPattern:
        {
                e->type = EXPRESSION_TAG_PATTERN;
                e->identifier = mkcstr(&v->items[0]);
                e->module = NULL;
                e->constraint = NULL;
                e->tagged = cexpr(&v->items[1]);
                break;
        }
        case TyCompileTime:
        {
                struct value v_ = *v;
                v_.tags = tags_pop(v_.tags);
                e->type = EXPRESSION_COMPILE_TIME;
                e->operand = cexpr(&v_);
                break;
        }
        case TyIfDef:
        {
                e->type = EXPRESSION_IFDEF;
                e->identifier = mkcstr(tuple_get(v, "name"));
                struct value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(mod) : NULL;
                break;
        }
        case TyDefined:
        {
                e->type = EXPRESSION_DEFINED;
                e->identifier = mkcstr(tuple_get(v, "name"));
                struct value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(mod) : NULL;
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
                e->statement = cstmt(v);
                if (e->filename == NULL && e->statement->filename != NULL) {
                        e->filename = e->statement->filename;
                        e->start = e->statement->start;
                        e->end = e->statement->end;
                }
                break;
        default:
        Bad:
                fail("invalid value passed to cexpr(): %s", value_show_color(v));
        }

        return e;
}

struct expression *
TyToCExpr(struct value *v)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return NULL;
        }

        struct expression *e = cexpr(v);

        RESTORE_JB;

        return e;
}

struct value
tyeval(struct expression *e)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return NONE;
        }

        if (!e->symbolized)
                symbolize_expression(state.macro_scope, e);

        byte_vector code_save = state.code;
        vec_init(state.code);

        location_vector locs_save = state.expression_locations;
        vec_init(state.expression_locations);

        emit_expression(e);
        emit_instr(INSTR_HALT);

        RESTORE_JB;

        size_t n_location_lists = location_lists.count;

        add_location_info();

        EvalDepth += 1;
        struct value v = vm_try_exec(state.code.items);
        EvalDepth -= 1;

        state.code = code_save;
        state.expression_locations = locs_save;

        location_lists.count = n_location_lists;

        return v;
}

struct expression *
typarse(struct expression *e, struct location const *start, struct location const *end)
{
        symbolize_expression(state.global, e);

        byte_vector code_save = state.code;
        vec_init(state.code);

        location_vector locs_save = state.expression_locations;
        vec_init(state.expression_locations);

        emit_expression(e);
        emit_instr(INSTR_HALT);

        add_location_info();

        vm_exec(state.code.items);

        state.code = code_save;
        state.expression_locations = locs_save;

        struct value m = *vm_get(0);

        struct scope *macro_scope_save = state.macro_scope;
        state.macro_scope = state.global;

        struct location const mstart = state.mstart;
        struct location const mend = state.mend;
        state.mstart = *start;
        state.mend = *end;

        struct value expr = vm_call(&m, 0);
        vm_push(&expr);

        state.macro_scope = macro_scope_save;

        struct expression *e_ = cexpr(&expr);

        state.mstart = mstart;
        state.mend = mend;

        // Take `m` and `expr` off the stack
        vm_pop();
        vm_pop();

        return e_;
}

void
define_class(struct statement *s)
{
        if (scope_locally_defined(state.global, s->class.name)) {
                fail(
                        "redeclaration of class %s%s%s%s%s",
                        TERM(1),
                        TERM(34),
                        s->class.name,
                        TERM(22),
                        TERM(39)
                );
        }

        struct symbol *sym = addsymbol(state.global, s->class.name);
        sym->class = class_new(s->class.name, s->class.doc);
        sym->doc = s->class.doc;
        sym->cnst = true;
        s->class.symbol = sym->class;

        for (int i = 0; i < s->class.methods.count; ++i) {
                struct expression *m = s->class.methods.items[i];
                class_add_method(sym->class, m->name, PTR(m));
        }

        if (s->class.pub) {
                VPush(state.exports, s->class.name);
        }
}

void
define_function(struct statement *s)
{
        symbolize_lvalue(state.global, s->target, true, s->pub);
        s->target->symbol->doc = s->doc;
}

void
define_macro(struct statement *s, bool fun)
{
        symbolize_statement(state.global, s);
        if (fun)
                s->target->symbol->fun_macro = true;
        else
                s->target->symbol->macro = true;
        s->target->symbol->doc = s->doc;

        s->type = STATEMENT_FUNCTION_DEFINITION;

        byte_vector code_save = state.code;
        vec_init(state.code);

        emit_statement(s, false);

        emit_instr(INSTR_HALT);

        vm_exec(state.code.items);

        state.code = code_save;
}

bool
is_fun_macro(char const *module, char const *id)
{
        struct symbol *s = NULL;

        if (module == NULL) {
                s = scope_lookup(state.global, id);
        } else {
                struct scope *mod = search_import_scope(module);
                if (mod != NULL) {
                        s = scope_lookup(mod, id);
                }
        }

        return s != NULL && s->fun_macro;
}

bool
is_macro(char const *module, char const *id)
{
        struct symbol *s = NULL;

        if (module == NULL) {
                s = scope_lookup(state.global, id);
        } else {
                struct scope *mod = search_import_scope(module);
                if (mod != NULL) {
                        s = scope_lookup(mod, id);
                }
        }

        return s != NULL && s->macro;
}

bool
compiler_symbolize_expression(struct expression *e, struct scope *scope)
{
        SAVE_JB;

        if (setjmp(jb) != 0) {
                RESTORE_JB;
                return false;
        }

        if (scope == NULL) {
                symbolize_expression(state.global, e);
        } else {
                state.fscope = scope->function;
                symbolize_expression(scope, e);
        }

        e->symbolized = true;

        RESTORE_JB;

        return true;
}

void
compiler_clear_location(void)
{
        state.start = state.end = state.mstart = state.mend = Nowhere;
}

Value
compiler_render_template(struct expression *e)
{
        Value v;

        if (e->template.stmts.count == 1) {
                v = tystmt(e->template.stmts.items[0]);
                goto End;
        }

        struct array *a = value_array_new();

        for (size_t i = 0; i < e->template.stmts.count; ++i) {
                value_array_push(a, tystmt(e->template.stmts.items[i]));
        }

        v = tagged(TyMulti, ARRAY(a), NONE);

End:
        for (size_t i = 0; i < e->template.exprs.count; ++i) {
                vm_pop();
        }

        return v;
}

/* vim: set sw=8 sts=8 expandtab: */
