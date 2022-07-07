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

#define EXPR(...) ((struct expression){ .start = { -1, -1 }, __VA_ARGS__ })

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
};

struct module {
        char const *path;
        char *code;
        struct scope *scope;
};

struct import {
        char const *name;
        struct scope *scope;
};

typedef vec(struct import)    import_vector;
typedef vec(struct eloc)      location_vector;
typedef vec(struct symbol *)  symbol_vector;
typedef vec(size_t)           offset_vector;
typedef vec(char)             byte_vector;
typedef vec(unsigned)         info_vector;

/*
 * State which is local to a single compilation unit.
 */
struct state {
        byte_vector code;

        offset_vector selfs;
        offset_vector breaks;
        offset_vector continues;
        offset_vector match_fails;
        offset_vector match_successes;

        symbol_vector bound_symbols;

        struct scope *method;
        struct scope *fscope;

        struct scope *macro_scope;

        struct scope *implicit_fscope;
        struct expression *implicit_func;

        struct expression *func;

        int function_depth;
        bool each_loop;
        bool loop_want_result;

        int finally;
        int try;
        int loop;

        import_vector imports;
        vec(char const *) exports;

        struct scope *global;

        char const *filename;
        struct location start;
        struct location end;

        location_vector expression_locations;
};

bool CheckConstraints = true;

static jmp_buf jb;
static char const *Error;

static int builtin_modules;
static int BuiltinCount;

static int jumpdistance;
static vec(struct module) modules;
static struct state state;

static vec(location_vector) location_lists;

static struct scope *global;

static uint64_t t;

static char const EmptyString[] = { '\0', '\0' };
static struct location Nowhere = { 0, 0, EmptyString + 1 };

static void
symbolize_statement(struct scope *scope, struct statement *s);

static void
symbolize_pattern(struct scope *scope, struct expression *e, bool def);

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

static struct scope *
get_import_scope(char const *);

static struct scope *
search_import_scope(char const *);

void
import_module(struct statement const *s);

static void
invoke_macro(struct expression *e, struct scope *scope);

static void
compile(char const *source);

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
                "\n\t%*s%s%s",
                before + 35,
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

inline static void
_emit_instr(char c)
{
        vec_push(state.code, c);
}

static char *
slurp_module(char const *name)
{
        char pathbuf[512];
        char const *home = getenv("HOME");
        if (home == NULL)
                fail("unable to get $HOME from the environment");

        snprintf(pathbuf, sizeof pathbuf, "%s/.ty/%s.ty", home, name);

        char *source = slurp(pathbuf);
        if (source == NULL) {
                snprintf(pathbuf, sizeof pathbuf, "%s.ty", name);
                source = slurp(pathbuf);
        }

        if (source == NULL) {
                fail("failed to read file: %s", pathbuf);
        }

        return source;
}

static void
add_location(struct expression const *e, size_t start_off, size_t end_off)
{
        if (e->start.line == -1 && e->start.col == -1)
                return;

        //printf("Location: (%zu, %zu) (%d) '%.*s'\n", start_off, end_off, e->type, (int)(e->end.s - e->start.s), e->start.s);

        vec_push(
                state.expression_locations,
                ((struct eloc) {
                        .start_off = start_off,
                        .end_off = end_off,
                        .start = e->start,
                        .end = e->end,
                        .filename = state.filename
                })
        );
}

static void
patch_location_info(void)
{
        struct eloc *locs = state.expression_locations.items;
        for (int i = 0; i < state.expression_locations.count; ++i) {
                locs[i].p_start = (uintptr_t)(state.code.items + locs[i].start_off);
                locs[i].p_end = (uintptr_t)(state.code.items + locs[i].end_off);
        }
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
is_class(struct expression const *e)
{
        assert(e->type == EXPRESSION_IDENTIFIER);

        struct scope const *scope = (e->module == NULL || *e->module == '\0') ? state.global : get_import_scope(e->module);
        struct symbol *sym = scope_lookup(scope, e->identifier);

        return sym != NULL && sym->class != -1;
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
                if (args[i]->type == EXPRESSION_SPREAD || conds[i] != NULL) {
                        return true;
                }
        }

        return false;
}

inline static struct symbol *
addsymbol(struct scope *scope, char const *name)
{
        assert(name != NULL);

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

        if (scope->function == global && isupper(name[0])) {
            vec_push(state.exports, name);
        }

        LOG("adding symbol: %s -> %d\n", name, s->symbol);

        return s;
}

inline static struct symbol *
getsymbol(struct scope const *scope, char const *name, bool *local)
{
        /*
         * _ can never be used as anything but an lvalue.
         */
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
                        char *id = sclone(b);
                        struct symbol *sym = addsymbol(state.implicit_fscope, id);
                        vec_push(state.implicit_func->params, id);
                        vec_push(state.implicit_func->param_symbols, sym);
                        vec_push(state.implicit_func->dflts, NULL);
                        vec_push(state.implicit_func->constraints, NULL);
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

/*
        if (scope_locally_defined(global, idbuf))
                return scope_lookup(global, idbuf);
        else
*/
                return scope_add(scope, sclone(idbuf));
}

static struct state
freshstate(void)
{
        struct state s;

        vec_init(s.code);

        vec_init(s.selfs);
        vec_init(s.bound_symbols);

        vec_init(s.breaks);
        vec_init(s.continues);

        vec_init(s.imports);
        vec_init(s.exports);

        s.method = NULL;
        s.global = scope_new(global, false);
        s.fscope = NULL;

        s.func = NULL;
        s.implicit_func = NULL;
        s.implicit_fscope = NULL;

        s.macro_scope = NULL;

        s.function_depth = 0;
        s.each_loop = false;
        s.loop_want_result = false;

        s.finally = false;

        s.try = 0;
        s.loop = 0;

        s.filename = NULL;
        s.start = s.end = Nowhere;

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

        vec_push(mod, '\0');

        char const *name = (e->type == EXPRESSION_MEMBER_ACCESS) ? e->member_name : e->method_name;
        struct location start = e->start;
        struct location end = e->end;

        e = e->object;

        while (e->type == EXPRESSION_MEMBER_ACCESS) {
                vec_insert_n(mod, e->member_name, strlen(e->member_name), 0);
                vec_insert(mod, '/', 0);
                e = e->object;
        }

        if (e->type != EXPRESSION_IDENTIFIER || e->module != NULL) {
                return NULL;
        }

        if (scope_lookup(scope, e->identifier) != NULL) {
                return NULL;
        }

        struct expression *id = gc_alloc(sizeof *id);

        id->start = start;
        id->end = end;
        id->identifier = (char *)name;
        id->type = EXPRESSION_IDENTIFIER;
        id->constraint = NULL;
        id->tagged = NULL;

        vec_insert_n(mod, e->identifier, strlen(e->identifier), 0);

        struct scope *mod_scope = search_import_scope(mod.items);

        if (mod_scope != NULL) {
                id->module = sclone(mod.items);
                id->symbol = getsymbol(mod_scope, name, &id->local);
                return id;
        } else {
                gc_free(id);
                return NULL;
        }
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
symbolize_methods(struct scope *scope, struct expression **ms, int n)
{
        for (int i = 0; i < n; ++i) {
                /*
                 * Here we temporarily set the method names to NULL. Say for example there is
                 * a method named 'print'. Within the method body, we don't want 'print' to refer
                 * to the method. Methods should only be accessible through tags or tagged values.
                 * That is, standalone identifiers should never resolve to methods. By setting the
                 * name to NULL before passing it to symbolize_expression, we avoid adding it as an
                 * identifier to the scope of the method body.
                 */
                char *name = ms[i]->name;
                ms[i]->name = NULL;

                ms[i]->is_method = true;
                symbolize_expression(scope, ms[i]);

                ms[i]->name = name;
        }
}

static void
add_captures(struct expression *pattern, struct scope *scope)
{
        /*
         * /(\w+) = (\d+)/ => $0, $1, $2
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
                addsymbol(scope, sclone(id));
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

                fc.function = mod_access;

                *e = fc;
        }

        if (e->type == EXPRESSION_FUNCTION_CALL && e->function->type == EXPRESSION_IDENTIFIER) {
                symbolize_expression(scope, e->function);
                if (e->function->symbol->tag != -1) {
                        struct expression f = *e;
                        char *identifier = e->function->identifier;
                        char *module = e->function->module;
                        struct expression **tagged = e->args.items;
                        int tagc = e->args.count;
                        struct symbol *symbol = e->function->symbol;
                        e->type = EXPRESSION_TAG_APPLICATION;
                        e->identifier = identifier;
                        e->module = module;
                        e->symbol = symbol;
                        if (tagc == 1 && tagged[0]->type != EXPRESSION_MATCH_REST) {
                                e->tagged = tagged[0];
                        } else {
                                struct expression *items = gc_alloc(sizeof *items);
                                items->type = EXPRESSION_TUPLE;
                                items->start = tagged[0]->start;
                                items->end = tagged[tagc - 1]->end;
                                vec_init(items->es);
                                vec_init(items->tconds);
                                vec_init(items->required);
                                vec_init(items->names);
                                for (int i = 0; i < tagc; ++i) {
                                        vec_push(items->es, tagged[i]);
                                        vec_push(items->tconds, NULL);
                                        vec_push(items->required, true);
                                        vec_push(items->names, NULL);
                                }
                                for (int i = 0; i < f.kws.count; ++i) {
                                        vec_push(items->es, f.kwargs.items[i]);
                                        vec_push(items->tconds, f.fkwconds.items[i]);
                                        vec_push(items->required, true);
                                        vec_push(items->names, f.kws.items[i]);
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
symbolize_lvalue(struct scope *scope, struct expression *target, bool decl, bool pub)
{
        state.start = target->start;
        state.end = target->end;

        if (target->type & EXPRESSION_SYMBOLIZED)
                return;

        struct expression *mod_access;

        try_symbolize_application(scope, target);

        switch (target->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
                if (decl) {
                        target->symbol = addsymbol(scope, target->identifier);
                        target->local = true;
                        symbolize_expression(scope, target->constraint);
                        if (pub) {
                                vec_push(state.exports, target->identifier);
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
                break;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_expression(scope, target->left);
                symbolize_lvalue(scope, target->right, decl, pub);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_lvalue(scope, target->tagged, decl, pub);
                target->symbol = getsymbol(
                        ((target->module == NULL || *target->module == '\0') ? state.global : get_import_scope(target->module)),
                        target->identifier,
                        NULL
                );
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < target->elements.count; ++i)
                        symbolize_lvalue(scope, target->elements.items[i], decl, pub);
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
                        symbolize_lvalue(scope, target->values.items[i], decl, pub);
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
                        gc_free(mod_access);
                        goto ConstAssignment;
                } else {
                        symbolize_expression(scope, target->object);
                }
                break;
        case EXPRESSION_TUPLE:
                target->ltmp = tmpsymbol(scope);
        case EXPRESSION_LIST:
                for (int i = 0; i < target->es.count; ++i) {
                        symbolize_lvalue(scope, target->es.items[i], decl, pub);
                }
                break;
        }
}

static void
symbolize_pattern(struct scope *scope, struct expression *e, bool def)
{
        if (e == NULL)
                return;

        if (e->type & EXPRESSION_SYMBOLIZED)
                return;

        try_symbolize_application(scope, e);

        if (e->type == EXPRESSION_IDENTIFIER && is_tag(e))
                goto Tag;

        state.start = e->start;
        state.end = e->end;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (strcmp(e->identifier, "_") != 0 && (is_const(scope, e->identifier) || scope_locally_defined(scope, e->identifier) || e->module != NULL)) {
                        e->type = EXPRESSION_MUST_EQUAL;
                        struct scope *s = (e->module == NULL || *e->module == '\0') ? scope : get_import_scope(e->module);
                        e->symbol = getsymbol(s, e->identifier, NULL);
                } else {
        case EXPRESSION_MATCH_NOT_NIL:
                        e->symbol = def ? addsymbol(scope, e->identifier) : getsymbol(scope, e->identifier, NULL);
                        symbolize_expression(scope, e->constraint);
                }
                e->local = true;
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < e->elements.count; ++i)
                        symbolize_pattern(scope, e->elements.items[i], def);
                break;
        case EXPRESSION_DICT:
                for (int i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(scope, e->keys.items[i]);
                        symbolize_pattern(scope, e->values.items[i], def);
                }
                break;
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        symbolize_pattern(scope, e->es.items[i], def);
                }
                break;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                symbolize_expression(scope, e->left);
                symbolize_pattern(scope, e->right, def);
                break;
        case EXPRESSION_SPREAD:
                assert(e->value->type == EXPRESSION_IDENTIFIER);
                e->type = EXPRESSION_MATCH_REST;
                e->identifier = e->value->identifier;
        case EXPRESSION_MATCH_REST:
                e->symbol = addsymbol(scope, e->identifier);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_pattern(scope, e->tagged, def);
                break;
        Tag:
                symbolize_expression(scope, e);
                e->type = EXPRESSION_MUST_EQUAL;
                break;
        case EXPRESSION_CHECK_MATCH:
                symbolize_pattern(scope, e->left, def);
                symbolize_expression(scope, e->right);
                break;
        default:
                symbolize_expression(scope, e);
                break;
        }
}

static void
symbolize_expression(struct scope *scope, struct expression *e)
{
        if (e == NULL)
                return;

        if (e->type & EXPRESSION_SYMBOLIZED)
                return;

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
                        subscope = scope_new(scope, false);
                        if (e->patterns.items[i]->type == EXPRESSION_REGEX) {
                                add_captures(e->patterns.items[i], subscope);
                        }
                        symbolize_pattern(subscope, e->patterns.items[i], true);
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
        case EXPRESSION_FUNCTION_CALL:
                symbolize_expression(scope, e->function);
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
                        gc_free(mod_access);
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

                        fc.function = mod_access;

                        *e = fc;

                        symbolize_expression(scope, e);
                } else {
                        symbolize_expression(scope, e->object);
                        for (size_t i = 0;  i < e->method_args.count; ++i)
                                symbolize_expression(scope, e->method_args.items[i]);
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
        case EXPRESSION_FUNCTION:
                state.func = e;

                if (e->name != NULL) {
                        scope = scope_new(scope, false);
                        e->function_symbol = addsymbol(scope, e->name);
                        LOG("== SYMBOLIZING %s ==", e->name);
                } else {
                        LOG("== SYMBOLIZING %s ==", "(anon)");
                        e->function_symbol = NULL;
                }

                scope = scope_new(scope, true);

                if (e->type == EXPRESSION_IMPLICIT_FUNCTION) {
                        state.implicit_fscope = scope;
                        state.implicit_func = e;
                        e->type = EXPRESSION_FUNCTION;
                }

                vec_init(e->param_symbols);

                for (size_t i = 0; i < e->params.count; ++i) {
                        symbolize_expression(scope, e->dflts.items[i]);
                        vec_push(e->param_symbols, addsymbol(scope, e->params.items[i]));
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

                if (e->ftype == FT_GEN) {
                        e->type = EXPRESSION_GENERATOR;
                }

                state.func = func;
                state.implicit_fscope = implicit_fscope;
                state.implicit_func = implicit_func;

                break;
        case EXPRESSION_WITH:
                subscope = scope_new(scope, false);
                symbolize_statement(subscope, e->with.let);
                for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                        for (struct symbol *sym = subscope->table[i]; sym != NULL; sym = sym->next) {
                                // Make sure it's not a tmpsymbol() symbol
                                if (!isdigit(sym->identifier[0])) {
                                        vec_push(e->with.block->statements.items[1]->try.finally->drop, sym);
                                }
                        }
                }
                symbolize_statement(subscope, e->with.block->statements.items[1]);
                break;
        case EXPRESSION_YIELD:
                if (state.func->ftype == FT_FUNC) {
                        fail("yield expression cannot appear outside of generator context");
                }
                for (int i = 0; i < e->es.count; ++i) {
                    symbolize_expression(scope, e->es.items[i]);
                }
                state.func->ftype = FT_GEN;
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i) {
                        symbolize_expression(scope, e->elements.items[i]);
                        symbolize_expression(scope, e->aconds.items[i]);
                }
                break;
        case EXPRESSION_ARRAY_COMPR:
                symbolize_expression(scope, e->compr.iter);
                subscope = scope_new(scope, false);
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
                subscope = scope_new(scope, false);
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
                vec_push_n(state.exports, s->exports.items, s->exports.count);
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
                if (s->class.super != NULL) {
                        symbolize_expression(scope, s->class.super);
                        if (!is_class(s->class.super))
                                fail("attempt to extend non-class");
                }
                subscope = scope_new(scope, false);
                symbolize_methods(subscope, s->class.methods.items, s->class.methods.count);
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
                subscope = scope_new(scope, false);
                symbolize_methods(subscope, s->tag.methods.items, s->tag.methods.count);
                break;
        case STATEMENT_BLOCK:
                scope = scope_new(scope, false);

                for (size_t i = 0; i < s->statements.count; ++i) {
                        symbolize_statement(scope, s->statements.items[i]);
                }

                break;
        case STATEMENT_MULTI:
                for (size_t i = 0; i < s->statements.count; ++i) {
                        symbolize_statement(scope, s->statements.items[i]);
                }
                break;
        case STATEMENT_THROW:
                symbolize_expression(scope, s->throw);
                break;
        case STATEMENT_TRY:
        {
                symbolize_statement(scope, s->try.s);

                for (int i = 0; i < s->try.patterns.count; ++i) {
                        struct scope *catch = scope_new(scope, false);
                        symbolize_pattern(catch, s->try.patterns.items[i], true);
                        symbolize_statement(catch, s->try.handlers.items[i]);
                }

                symbolize_statement(scope, s->try.finally);

                break;

        }
        case STATEMENT_WHILE_MATCH:
        case STATEMENT_MATCH:
                symbolize_expression(scope, s->match.e);
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        subscope = scope_new(scope, false);
                        if (s->match.patterns.items[i]->type == EXPRESSION_REGEX) {
                                add_captures(s->match.patterns.items[i], subscope);
                        }
                        symbolize_pattern(subscope, s->match.patterns.items[i], true);
                        symbolize_statement(subscope, s->match.statements.items[i]);
                }
                break;
        case STATEMENT_WHILE:
                subscope = scope_new(scope, false);
                for (int i = 0; i < s->While.parts.count; ++i) {
                        struct condpart *p = s->While.parts.items[i];
                        symbolize_expression(subscope, p->e);
                        symbolize_pattern(subscope, p->target, p->def);
                }
                symbolize_statement(subscope, s->While.block);
                break;
        case STATEMENT_IF:
                // if not let Ok(x) = f() or not [y] = bar() {
                subscope = scope_new(scope, false);
                if (s->iff.neg) {
                        symbolize_statement(scope, s->iff.then);
                        for (int i = 0; i < s->iff.parts.count; ++i) {
                                struct condpart *p = s->iff.parts.items[i];
                                symbolize_pattern(scope, p->target, p->def);
                                symbolize_expression(subscope, p->e);
                        }
                        symbolize_statement(subscope, s->iff.otherwise);
                } else {
                        symbolize_statement(subscope, s->iff.otherwise);
                        for (int i = 0; i < s->iff.parts.count; ++i) {
                                struct condpart *p = s->iff.parts.items[i];
                                symbolize_expression(subscope, p->e);
                                symbolize_pattern(subscope, p->target, p->def);

                        }
                        symbolize_statement(subscope, s->iff.then);
                }
                break;
        case STATEMENT_FOR_LOOP:
                scope = scope_new(scope, false);
                symbolize_statement(scope, s->for_loop.init);
                symbolize_expression(scope, s->for_loop.cond);
                symbolize_expression(scope, s->for_loop.next);
                symbolize_statement(scope, s->for_loop.body);
                break;
        case STATEMENT_EACH_LOOP:
                symbolize_expression(scope, s->each.array);
                subscope = scope_new(scope, false);
                symbolize_lvalue(subscope, s->each.target, true, false);
                symbolize_statement(subscope, s->each.body);
                symbolize_expression(subscope, s->each.cond);
                symbolize_expression(subscope, s->each.stop);
                break;
        case STATEMENT_RETURN:
                if (state.func->ftype == FT_GEN) {
                        fail("return statement cannot appear in generator context");
                }
                for (int i = 0; i < s->returns.count; ++i) {
                    symbolize_expression(scope, s->returns.items[i]);
                }
                state.func->ftype = FT_FUNC;
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
                if (scope != state.global) {
        case STATEMENT_MACRO_DEFINITION:
                        symbolize_lvalue(scope, s->target, true, s->pub);
                }
                symbolize_expression(scope, s->value);
                break;
        }
}

static void
invoke_macro(struct expression *e, struct scope *scope)
{
        struct scope *macro_scope_save = state.macro_scope;
        state.macro_scope = scope;

        symbolize_expression(scope, e->macro.m);

        byte_vector code_save = state.code;

        vec_init(state.code);

        emit_expression(e->macro.m);
        emit_instr(INSTR_HALT);

        vm_exec(state.code.items);

        struct value m = *vm_get(0);
        vm_pop();

        gc_free(state.code.items);
        state.code = code_save;

        struct value node = tyexpr(e->macro.e);
        vm_push(&node);

        node = vm_call(&m, 1);

        state.macro_scope = macro_scope_save;

        struct expression *result = cexpr(&node);

        symbolize_expression(scope, result);

        *e = *result;

        gc_free(result);
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
        patch_jumps_to(&state.continues, begin);
        patch_jumps_to(&state.breaks, end);
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
                vec_push(state.code, s[i]);
}

inline static void
emit_int16(int16_t k)
{
        LOG("emitting int16_t: %d", (int)k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (int16_t); ++i)
                vec_push(state.code, s[i]);
}

inline static void
emit_ulong(unsigned long k)
{
        LOG("emitting ulong: %lu", k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (unsigned long); ++i)
                vec_push(state.code, s[i]);
}

inline static void
emit_symbol(uintptr_t sym)
{
        LOG("emitting symbol: %"PRIuPTR, sym);
        char const *s = (char *) &sym;
        for (int i = 0; i < sizeof (uintptr_t); ++i)
                vec_push(state.code, s[i]);
}

inline static void
emit_integer(intmax_t k)
{

        LOG("emitting integer: %"PRIiMAX, k);
        vec_push_n(state.code, (char const *)&k, sizeof k);
}

inline static void
emit_boolean(bool b)
{

        LOG("emitting boolean: %s", b ? "true" : "false");
        char const *s = (char *) &b;
        for (int i = 0; i < sizeof (bool); ++i)
                vec_push(state.code, s[i]);
}

inline static void
emit_float(float f)
{

        LOG("emitting float: %f", f);
        vec_push_n(state.code, (char const *)&f, sizeof f);
}

inline static void
emit_string(char const *s)
{

        LOG("emitting string: %s", s);
        vec_push_n(state.code, s, strlen(s) + 1);
}

inline static void
emit_load(struct symbol const *s, struct scope const *scope)
{
        bool local = !s->global && (s->scope->function == scope->function);

        LOG("Emitting LOAD for %s", s->identifier);

        if (s->global) {
                emit_instr(INSTR_LOAD_GLOBAL);
                emit_int(s->i);
        } else if (local && !s->captured) {
                emit_instr(INSTR_LOAD_LOCAL);
                emit_int(s->i);
        } else if (!local && s->captured) {
                LOG("It is captured and not owned by us");
                int i = 0;
                while (scope->function->captured.items[i] != s) {
                        LOG("Checking against %s", scope->function->captured.items[i]->identifier);
                        i += 1;
                }
                emit_instr(INSTR_LOAD_CAPTURED);
                emit_int(i);
        } else {
                emit_instr(INSTR_LOAD_REF);
                emit_int(s->i);
        }
}

inline static void
emit_tgt(struct symbol const *s, struct scope const *scope, bool def)
{
        bool local = !s->global && (s->scope->function == scope->function);

        if (s->global) {
                emit_instr(INSTR_TARGET_GLOBAL);
                emit_int(s->i);
        } else if (def || (local && !s->captured)) {
                emit_instr(INSTR_TARGET_LOCAL);
                emit_int(s->i);
        } else if (!local && s->captured) {
                int i = 0;
                while (scope->function->captured.items[i] != s) {
                        i += 1;
                }
                emit_instr(INSTR_TARGET_CAPTURED);
                emit_int(i);
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
        int loop_save = state.loop;
        int try_save = state.try;
        bool finally_save = state.finally;
        bool each_loop_save = state.each_loop;
        int t_save = t;
        state.loop = state.try = t = 0;
        state.each_loop = state.finally = false;

        struct scope *fs_save = state.fscope;
        state.fscope = e->scope;

        struct symbol **caps = e->scope->captured.items;
        int *cap_indices = e->scope->cap_indices.items;
        int ncaps = e->scope->captured.count;

        for (int i = ncaps - 1; i >= 0; --i) {
                if (cap_indices[i] == -1) {
                        /*
                         * Don't call emit_tgt because despite these being captured,
                         * we need to use TARGET_LOCAL to avoid following the reference.
                         */
                        emit_instr(INSTR_TARGET_LOCAL);
                        emit_int(caps[i]->i);
                } else {
                        // FIXME: should just use same allocated variable
                        emit_instr(INSTR_TARGET_CAPTURED);
                        emit_int(cap_indices[i]);
                }
        }

        emit_instr(INSTR_FUNCTION);

        while (((uintptr_t)(state.code.items + state.code.count)) % (_Alignof (int)) != ((_Alignof (int)) - 1))
                vec_push(state.code, 0x00);
        vec_push(state.code, 0xFF);

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
                vec_push(state.code, 0x00);
        }

        emit_int(class);

        emit_string(e->name == NULL ? "(anonymous function)" : e->name);
        LOG("COMPILING FUNCTION: %s.%s", class == -1 ? "TOP" : class_name(class), (e->name == NULL ? "(anonymous function)" : e->name));

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
                emit_instr(INSTR_LOAD_LOCAL);
                emit_int(s->i);
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
                if (!CheckConstraints || e->constraints.items[i] == NULL)
                        continue;
                struct symbol const *s = e->param_symbols.items[i];
                size_t start = state.code.count;
                emit_instr(INSTR_LOAD_LOCAL);
                emit_int(s->i);
                emit_constraint(e->constraints.items[i]);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t good);
                emit_instr(INSTR_LOAD_LOCAL);
                emit_int(s->i);
                emit_instr(INSTR_BAD_CALL);
                if (e->name != NULL)
                        emit_string(e->name);
                else
                        emit_string("(anonymous function)");
                emit_string(e->param_symbols.items[i]->identifier);
                add_location(e->constraints.items[i], start, state.code.count);
                emit_instr(INSTR_POP);
                PATCH_JUMP(good);
        }

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
        } else {
                emit_statement(body, true);
                if (CheckConstraints && e->return_type != NULL) {
                        size_t start = state.code.count;
                        emit_instr(INSTR_DUP);
                        emit_constraint(e->return_type);
                        PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t good);
                        emit_instr(INSTR_BAD_CALL);
                        if (e->name != NULL)
                                emit_string(e->name);
                        else
                                emit_string("(anonymous function)");
                        emit_string("return value");
                        add_location(e->return_type, start, state.code.count);
                        PATCH_JUMP(good);
                }
                emit_instr(INSTR_RETURN);
        }

        while ((state.code.count - start_offset) % P_ALIGN != 0) {
                vec_push(state.code, 0x00);
        }

        int bytes = state.code.count - start_offset;
        memcpy(state.code.items + size_offset, &bytes, sizeof bytes);
        LOG("bytes in func = %d", bytes);

        for (int i = 0; i < ncaps; ++i) {
                bool local = caps[i]->scope->function == fs_save;
                emit_boolean(local);
        }

        state.fscope = fs_save;
        state.selfs = selfs_save;
        state.bound_symbols = syms_save;
        --state.function_depth;
        state.loop = loop_save;
        state.try = try_save;
        state.finally = finally_save;
        state.each_loop = each_loop_save;
        t = t_save;

        if (e->function_symbol != NULL) {
                emit_tgt(e->function_symbol, e->scope->parent, false);
                emit_instr(INSTR_ASSIGN);
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
                        vec_push_n(state.code, e->fmts.items[i], strcspn(e->fmts.items[i], "{"));
                }
                vec_push(state.code, '\0');
                emit_instr(INSTR_STRING);
                emit_string(e->strings.items[i + 1]);
        }

        emit_instr(INSTR_CONCAT_STRINGS);
        emit_int(2 * e->expressions.count + 1);
}

static bool
emit_throw(struct statement const *s)
{
        size_t start = state.code.count;

        emit_expression(s->throw);
        emit_instr(INSTR_THROW);

        add_location(&((struct expression){ .start = s->start, .end = s->end }), start, state.code.count);

        return true;
}

static void
emit_with(struct expression const *e)
{
        emit_statement(e->with.block, true);
}

static void
emit_yield(struct expression const *e)
{
        if (state.function_depth == 0) {
                fail("invalid yield expression (not inside of a function)");
        }

        if (e->es.count > 1) {
                fail("yielding multiple values isn't implemented yet");
        }

        if (e->es.count > 0) for (int i = 0; i < e->es.count; ++i) {
                emit_expression(e->es.items[i]);
                emit_instr(INSTR_TAG_PUSH);
                emit_int(TAG_SOME);
        } else {
                emit_instr(INSTR_NIL);
        }

        emit_instr(INSTR_YIELD);
}

static bool
emit_return(struct statement const *s)
{
        if (state.function_depth == 0) {
                fail("invalid return statement (not inside of a function)");
        }

        if (state.finally) {
                fail("invalid return statement (occurs in a finally block)");
        }

        /* returning from within a for-each loop must be handled specially */
        if (state.each_loop && s->type) {
                emit_instr(INSTR_POP);
                emit_instr(INSTR_POP);
        }

        if (false && s->returns.count == 1 && is_call(s->returns.items[0])) {
                emit_instr(INSTR_TAIL_CALL);
        }

        if (s->returns.count > 0) for (int i = 0; i < s->returns.count; ++i) {
                emit_expression(s->returns.items[i]);
        } else {
                emit_instr(INSTR_NIL);
        }

        if (state.try) {
                emit_instr(INSTR_FINALLY);
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

        int try_save = state.try;
        state.try = ++t;

        bool finally_save = state.finally;
        state.finally = false;

        if (s->type == STATEMENT_TRY_CLEAN) {
                emit_instr(INSTR_PUSH_DEFER_GROUP);
        }

        bool returns = emit_statement(s->try.s, want_result);

        emit_instr(INSTR_POP_TRY);

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

        state.try = try_save;
        state.finally = finally_save;

        if (s->try.finally != NULL) {
                PATCH_JUMP(finally_offset);
                state.finally = true;
                returns &= emit_statement(s->try.finally, false);
                state.finally = false;
                PATCH_JUMP(end_offset);
                emit_instr(INSTR_NOP);
        } else {
                returns = false;
        }

        return returns;
}

static void
emit_for_loop(struct statement const *s, bool want_result)
{
        offset_vector cont_save = state.continues;
        offset_vector brk_save = state.breaks;
        vec_init(state.continues);
        vec_init(state.breaks);

        bool loop_wr_save = state.loop_want_result;
        state.loop_want_result = want_result;

        bool each_loop_save = state.each_loop;
        state.each_loop = false;

        int loop_save = state.loop;
        state.loop = ++t;

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

        state.continues = cont_save;
        state.breaks = brk_save;
        state.loop_want_result = loop_wr_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_try_match(struct expression const *pattern)
{
        size_t start = state.code.count;
        bool need_loc = false;
        bool set = true;

        switch (pattern->type & ~EXPRESSION_SYMBOLIZED) {
        case EXPRESSION_IDENTIFIER:
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
                        vec_push(state.match_fails, state.code.count);
                        emit_int(0);
                }
                break;
        case EXPRESSION_CHECK_MATCH:
                emit_try_match(pattern->left);
                emit_instr(INSTR_DUP);
                emit_constraint(pattern->right);
                emit_instr(INSTR_JUMP_IF_NOT);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_tgt(pattern->symbol, state.fscope, true);
                emit_instr(INSTR_TRY_ASSIGN_NON_NIL);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                break;
        case EXPRESSION_MUST_EQUAL:
                emit_load(pattern->symbol, state.fscope);
                emit_instr(INSTR_ENSURE_EQUALS_VAR);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                need_loc = true;
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                emit_instr(INSTR_DUP);
                emit_instr(INSTR_JUMP_IF_NIL);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                // Fallthrough
        case EXPRESSION_VIEW_PATTERN:
                emit_instr(INSTR_DUP);
                emit_expression(pattern->left);
                emit_instr(INSTR_CALL);
                emit_int(1);
                emit_int(0);
                add_location(pattern->left, start, state.code.count);
                emit_try_match(pattern->right);
                emit_instr(INSTR_POP);
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < pattern->elements.count; ++i) {
                        if (pattern->elements.items[i]->type == EXPRESSION_MATCH_REST) {
                                emit_tgt(pattern->elements.items[i]->symbol, state.fscope, true);
                                emit_instr(INSTR_ARRAY_REST);
                                emit_int(i);
                                vec_push(state.match_fails, state.code.count);
                                emit_int(0);

                                if (i + 1 != pattern->elements.count)
                                        fail("the *<id> array-matching pattern must be the last pattern in the array");
                        } else {
                                emit_instr(INSTR_TRY_INDEX);
                                emit_int(i);
                                emit_boolean(!pattern->optional.items[i]);
                                vec_push(state.match_fails, state.code.count);
                                emit_int(0);

                                emit_try_match(pattern->elements.items[i]);

                                emit_instr(INSTR_POP);
                        }
                }

                if (pattern->elements.count == 0 ||
                    pattern->elements.items[pattern->elements.count - 1]->type != EXPRESSION_MATCH_REST) {
                        emit_instr(INSTR_ENSURE_LEN);
                        emit_int(pattern->elements.count);
                        vec_push(state.match_fails, state.code.count);
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
                        vec_push(state.match_fails, state.code.count);
                        emit_int(0);
                } else {
                        emit_instr(INSTR_ENSURE_DICT);
                        vec_push(state.match_fails, state.code.count);
                        emit_int(0);
                        for (int i = 0; i < pattern->keys.count; ++i) {
                                if (pattern->values.items[i] != NULL) {
                                        emit_instr(INSTR_DUP);
                                        emit_expression(pattern->keys.items[i]);
                                        emit_instr(INSTR_SUBSCRIPT);
                                        emit_try_match(pattern->values.items[i]);
                                        emit_instr(INSTR_POP);
                                } else {
                                        emit_expression(pattern->keys.items[i]);
                                        emit_instr(INSTR_ENSURE_CONTAINS);
                                        vec_push(state.match_fails, state.code.count);
                                        emit_int(0);
                                }
                        }
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_instr(INSTR_DUP);
                emit_instr(INSTR_TRY_TAG_POP);
                emit_int(pattern->symbol->tag);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);

                emit_try_match(pattern->tagged);

                emit_instr(INSTR_POP);
                break;
        case EXPRESSION_REGEX:
                emit_tgt(pattern->match_symbol, state.fscope, true);
                emit_instr(INSTR_TRY_REGEX);
                emit_symbol((uintptr_t) pattern->regex);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                need_loc = true;
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < pattern->es.count; ++i) {
                        if (pattern->es.items[i]->type == EXPRESSION_MATCH_REST) {
                                emit_tgt(pattern->es.items[i]->symbol, state.fscope, true);
                                emit_instr(INSTR_TUPLE_REST);
                                emit_int(i);
                                vec_push(state.match_fails, state.code.count);
                                emit_int(0);

                                if (i + 1 != pattern->es.count)
                                        fail("the *<id> tuple-matching pattern must be the last pattern in the tuple");
                        } else if (pattern->names.items[i] != NULL) {
                                emit_instr(INSTR_TRY_TUPLE_MEMBER);
                                emit_boolean(pattern->required.items[i]);
                                emit_string(pattern->names.items[i]);
                                vec_push(state.match_fails, state.code.count);
                                emit_int(0);
                                emit_try_match(pattern->es.items[i]);
                                emit_instr(INSTR_POP);
                        } else {
                                emit_instr(INSTR_TRY_INDEX_TUPLE);
                                emit_int(i);
                                vec_push(state.match_fails, state.code.count);
                                emit_int(0);
                                emit_try_match(pattern->es.items[i]);
                                emit_instr(INSTR_POP);
                        }
                }

                if (pattern->es.count == 0 || pattern->es.items[pattern->es.count - 1]->type != EXPRESSION_MATCH_REST) {
                        emit_instr(INSTR_ENSURE_LEN_TUPLE);
                        emit_int(pattern->es.count);
                        vec_push(state.match_fails, state.code.count);
                        emit_int(0);
                }

                break;
        case EXPRESSION_LIST:
                for (int i = 0; i < pattern->es.count; ++i) {
                        emit_instr(INSTR_PUSH_NTH);
                        emit_int(i);
                        emit_instr(INSTR_JUMP_IF_SENTINEL);
                        vec_push(state.match_fails, state.code.count);
                        emit_int(0);
                        emit_try_match(pattern->es.items[i]);
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
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                need_loc = true;
        }

        if (pattern->type > EXPRESSION_KEEP_LOC || need_loc)
                add_location(pattern, start, state.code.count);
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
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
        }

        emit_instr(INSTR_RESTORE_STACK_POS);
        emit_instr(INSTR_CLEAR_EXTRA);

        bool returns = false;

        emit_instr(INSTR_POP_TRY);
        emit_instr(INSTR_POP_THROW);

        if (s != NULL) {
                returns = emit_statement(s, want_result);
        } else if (want_result) {
                emit_instr(INSTR_NIL);
        }

        emit_instr(INSTR_JUMP);
        vec_push(state.match_successes, state.code.count);
        emit_int(0);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;

        return returns;
}

static bool
emit_case(struct expression const *pattern, struct expression const *cond, struct statement const *s, bool want_result)
{
        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        emit_instr(INSTR_SAVE_STACK_POS);
        emit_try_match(pattern);

        if (cond != NULL) {
                emit_expression(cond);
                emit_instr(INSTR_JUMP_IF_NOT);
                vec_push(state.match_fails, state.code.count);
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

        emit_instr(INSTR_JUMP);
        vec_push(state.match_successes, state.code.count);
        emit_int(0);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;

        return returns;
}

static void
emit_expression_case(struct expression const *pattern, struct expression const *e)
{
        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        emit_instr(INSTR_SAVE_STACK_POS);
        emit_try_match(pattern);

        /*
         * Go back to where the subject of the match is on top of the stack,
         * then pop it and execute the code to produce the result of this branch.
         */
        emit_instr(INSTR_RESTORE_STACK_POS);
        emit_instr(INSTR_CLEAR_EXTRA);
        emit_expression(e);

        /*
         * We've successfully matched a pattern+condition and produced a result, so we jump
         * to the end of the match expression. i.e., there is no fallthrough.
         */
        emit_instr(INSTR_JUMP);
        vec_push(state.match_successes, state.code.count);
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

        emit_list(s->match.e);
        emit_instr(INSTR_FIX_EXTRA);

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
        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;

        bool each_loop_save = state.each_loop;
        state.each_loop = false;

        bool loop_wr_save = state.loop_want_result;
        state.loop_want_result = want_result;

        int loop_save = state.loop;
        state.loop = ++t;

        vec_init(state.breaks);
        vec_init(state.continues);
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
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop_want_result = loop_wr_save;
        state.loop = loop_save;
}

static bool
emit_while(struct statement const *s, bool want_result)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);

        offset_vector cont_save = state.continues;
        offset_vector brk_save = state.breaks;

        bool each_loop_save = state.each_loop;
        state.each_loop = false;

        bool loop_wr_save = state.loop_want_result;
        state.loop_want_result = want_result;

        int loop_save = state.loop;
        state.loop = ++t;

        vec_init(state.continues);
        vec_init(state.breaks);

        size_t start = state.code.count;

        for (int i = 0; i < s->While.parts.count; ++i) {
                struct condpart *p = s->While.parts.items[i];
                if (p->target == NULL) {
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_expression(p->e);
                        emit_instr(INSTR_JUMP_IF_NOT);
                        vec_push(state.match_fails, state.code.count);
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

        emit_statement(s->While.block, false);

        JUMP(start);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        if (want_result) {
                emit_instr(INSTR_NIL);
        }

        patch_loop_jumps(start, state.code.count);

        state.continues = cont_save;
        state.breaks = brk_save;
        state.each_loop = each_loop_save;
        state.loop_want_result = loop_wr_save;
        state.loop = loop_save;

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

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (p->target == NULL) {
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_expression(p->e);
                        emit_instr(INSTR_JUMP_IF);
                        vec_push(state.match_fails, state.code.count);
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

        for (int i = 0; i < s->iff.parts.count; ++i) {
                struct condpart *p = s->iff.parts.items[i];
                if (p->target == NULL) {
                        emit_instr(INSTR_SAVE_STACK_POS);
                        emit_expression(p->e);
                        emit_instr(INSTR_JUMP_IF_NOT);
                        vec_push(state.match_fails, state.code.count);
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

        state.match_successes = successes_save;
        state.match_fails = fails_save;

        return returns;
}

static void
emit_match_expression(struct expression const *e)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        emit_list(e->subject);
        emit_instr(INSTR_FIX_EXTRA);

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
        bool need_loc = true;

        switch (target->type & ~EXPRESSION_SYMBOLIZED) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
                need_loc = false;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_tgt(target->symbol, state.fscope, def);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                LOG("MEMBER ACCESS: %s", target->member_name);
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

        if (need_loc)
                add_location(target, start, state.code.count);
}

static void
emit_dict_compr2(struct expression const *e)
{
        bool each_loop_save = state.each_loop;
        state.each_loop = true;

        int loop_save = state.loop;
        state.loop = ++t;

        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        offset_vector fails_save = state.match_fails;
        vec_init(state.breaks);
        vec_init(state.continues);
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
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_dict_compr(struct expression const *e)
{
        bool each_loop_save = state.each_loop;
        state.each_loop = true;

        int loop_save = state.loop;
        state.loop = ++t;

        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        vec_init(state.breaks);
        vec_init(state.continues);
        vec_init(state.match_successes);

        emit_instr(INSTR_DICT);
        emit_int(0);

        emit_instr(INSTR_PUSH_INDEX);
        if (e->dcompr.pattern->type == EXPRESSION_LIST) {
                emit_int((int)e->dcompr.pattern->es.count);
        } else {
                emit_int(1);
        }

        emit_expression(e->dcompr.iter);

        size_t start = state.code.count;

        for (int i = 0; i < e->dcompr.pattern->es.count; ++i) {
                emit_target(e->dcompr.pattern->es.items[i], true);
        }

        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_instr(INSTR_GET_NEXT);
        emit_instr(INSTR_READ_INDEX);
        emit_instr(INSTR_MULTI_ASSIGN);
        emit_int((int)e->dcompr.pattern->es.count);
        emit_instr(INSTR_NIL);
        emit_instr(INSTR_EQ);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t stop);
        if (e->dcompr.cond != NULL) {
                emit_expression(e->dcompr.cond);
                JUMP_IF_NOT(start);
        }
        for (int i = e->keys.count - 1; i >= 0; --i) {
                emit_expression(e->keys.items[i]);
                if (e->values.items[i] != NULL)
                        emit_expression(e->values.items[i]);
                else
                        emit_instr(INSTR_NIL);

        }
        emit_instr(INSTR_DICT_COMPR);
        emit_int((int)e->keys.count);
        JUMP(start);
        PATCH_JUMP(stop);
        patch_loop_jumps(start, state.code.count);
        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_array_compr2(struct expression const *e)
{
        bool each_loop_save = state.each_loop;
        state.each_loop = true;

        int loop_save = state.loop;
        state.loop = ++t;

        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        offset_vector fails_save = state.match_fails;
        vec_init(state.breaks);
        vec_init(state.continues);
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
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_array_compr(struct expression const *e)
{
        bool each_loop_save = state.each_loop;
        state.each_loop = true;

        int loop_save = state.loop;
        state.loop = ++t;

        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        vec_init(state.breaks);
        vec_init(state.continues);
        vec_init(state.match_successes);

        emit_instr(INSTR_ARRAY);
        emit_int(0);

        emit_instr(INSTR_PUSH_INDEX);
        if (e->compr.pattern->type == EXPRESSION_LIST) {
                emit_int((int)e->compr.pattern->es.count);
        } else {
                emit_int(1);
        }

        emit_expression(e->compr.iter);

        size_t start = state.code.count;

        for (int i = 0; i < e->compr.pattern->es.count; ++i) {
                emit_target(e->compr.pattern->es.items[i], true);
        }

        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_instr(INSTR_GET_NEXT);
        emit_instr(INSTR_READ_INDEX);
        emit_instr(INSTR_MULTI_ASSIGN);
        emit_int((int)e->compr.pattern->es.count);
        emit_instr(INSTR_NIL);
        emit_instr(INSTR_EQ);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t stop);
        if (e->compr.cond != NULL) {
                emit_expression(e->compr.cond);
                JUMP_IF_NOT(start);
        }
        for (int i = e->elements.count - 1; i >= 0; --i)
                emit_expression(e->elements.items[i]);
        emit_instr(INSTR_ARRAY_COMPR);
        emit_int((int)e->elements.count);
        JUMP(start);
        PATCH_JUMP(stop);
        patch_loop_jumps(start, state.code.count);
        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_spread(struct expression const *e, bool nils)
{
        emit_instr(INSTR_PUSH_INDEX);
        emit_int(1);

        emit_expression(e->value);

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
        bool each_loop_save = state.each_loop;
        state.each_loop = true;

        bool loop_wr_save = state.loop_want_result;
        state.loop_want_result = want_result;

        int loop_save = state.loop;
        state.loop = ++t;

        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        offset_vector fails_save = state.match_fails;
        vec_init(state.breaks);
        vec_init(state.continues);
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

        add_location(s->each.array, start, state.code.count);

        size_t match, done;
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, done);

        emit_instr(INSTR_FIX_TO);
        emit_int((int)s->each.target->es.count);

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
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop_want_result = loop_wr_save;
        state.loop = loop_save;
}

static void
emit_for_each(struct statement const *s)
{
        bool each_loop_save = state.each_loop;
        state.each_loop = true;

        int loop_save = state.loop;
        state.loop = ++t;

        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        vec_init(state.breaks);
        vec_init(state.continues);
        vec_init(state.match_successes);

        emit_instr(INSTR_PUSH_INDEX);
        if (s->each.target->type == EXPRESSION_LIST) {
                emit_int((int)s->each.target->es.count);
        } else {
                emit_int(1);
        }

        emit_expression(s->each.array);

        size_t start = state.code.count;

        for (int i = 0; i < s->each.target->es.count; ++i) {
                emit_target(s->each.target->es.items[i], true);
        }

        emit_instr(INSTR_SENTINEL);
        emit_instr(INSTR_CLEAR_RC);
        emit_instr(INSTR_GET_NEXT);
        emit_instr(INSTR_READ_INDEX);
        emit_instr(INSTR_MULTI_ASSIGN);
        emit_int((int)s->each.target->es.count);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NONE, size_t stop);
        emit_statement(s->each.body, false);
        JUMP(start);
        PATCH_JUMP(stop);
        patch_loop_jumps(start, state.code.count);
        emit_instr(INSTR_POP);
        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
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
        char multi = maybe ? INSTR_MAYBE_MULTI : INSTR_MULTI_ASSIGN;

        size_t start = state.code.count;

        switch (target->type & ~EXPRESSION_SYMBOLIZED) {
        case EXPRESSION_ARRAY:
                for (int i = 0; i < target->elements.count; ++i) {
                        if (target->elements.items[i]->type == EXPRESSION_MATCH_REST) {
                                // might use later
                                int after = target->elements.count - (i + 1);

                                emit_target(target->elements.items[i], def);

                                emit_instr(INSTR_ARRAY_REST);
                                emit_int(i);
                                emit_int(sizeof (int) + 1);
                                emit_instr(INSTR_JUMP);
                                emit_int(1);
                                emit_instr(INSTR_BAD_MATCH);
                        } else {
                                emit_instr(INSTR_PUSH_ARRAY_ELEM);
                                emit_int(i);
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
        case EXPRESSION_MATCH_NOT_NIL:
                emit_instr(INSTR_THROW_IF_NIL);
                emit_target(target, def);
                emit_instr(instr);
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < target->es.count; ++i) {
                        if (target->es.items[i]->type == EXPRESSION_MATCH_REST) {
                                // might use later
                                int after = target->es.count - (i + 1);

                                emit_target(target->es.items[i], def);

                                emit_instr(INSTR_TUPLE_REST);
                                emit_int(i);
                                emit_int(sizeof (int) + 1);
                                emit_instr(INSTR_JUMP);
                                emit_int(1);
                                emit_instr(INSTR_BAD_MATCH);
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
                if (target->type == EXPRESSION_IDENTIFIER && target->constraint != NULL) {
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

                // Don't need location info, can't fail here
                return;
        }

        add_location(target, start, state.code.count);
}

static void
emit_assignment(struct expression *target, struct expression const *e, bool maybe, bool def)
{
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
        int ac;

        char const *method = NULL;

        void (*emit)(struct expression const *);

        switch (e->type & ~EXPRESSION_SYMBOLIZED) {
        case EXPRESSION_IDENTIFIER:
                emit_load(e->symbol, state.fscope);
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
        case EXPRESSION_TAG:
                emit_instr(INSTR_TAG);
                emit_int(e->symbol->tag);
                break;
        case EXPRESSION_REGEX:
                emit_instr(INSTR_REGEX);
                emit_symbol((uintptr_t) e->regex);
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
                                emit_spread(e->keys.items[i], true);
                        } else {
                                emit_expression(e->keys.items[i]);
                                if (e->values.items[i] == NULL)
                                        emit_instr(INSTR_NIL);
                                else
                                        emit_expression(e->values.items[i]);
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
                        if (e->fconds.items[i] != NULL) {
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
                        if (e->mconds.items[i] != NULL) {
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
                emit_yield(e);
                break;
        case EXPRESSION_SPREAD:
                emit_spread(e, false);
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
        case EXPRESSION_FUNCTION:
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
                                vec_push(state.code, 0);
                        }
                }
                break;
        default:
                fail("expression unexpected in this context");
        }

        if (e->type > EXPRESSION_KEEP_LOC || need_loc)
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
                for (int i = 0; i < s->class.methods.count; ++i) {
                        state.method = s->class.methods.items[i]->scope;
                        emit_function(s->class.methods.items[i], s->class.symbol);
                }

                emit_instr(INSTR_DEFINE_CLASS);
                emit_int(s->class.symbol);
                emit_int(s->class.super == NULL ? 0 : s->class.super->symbol->class);
                emit_int(s->class.methods.count);

                for (int i = s->class.methods.count; i > 0; --i)
                        emit_string(s->class.methods.items[i - 1]->name);

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
        case STATEMENT_THROW:
                if (state.finally) {
                        fail("invalid 'throw' statement (occurs in a finally block)");
                }
                returns |= emit_throw(s);
                break;
        case STATEMENT_RETURN_GENERATOR:
        case STATEMENT_RETURN:
                returns |= emit_return(s);
                break;
        case STATEMENT_BREAK:
                if (state.loop == 0) {
                        fail("invalid break statement (not inside a loop)");
                }

                if (state.try > state.loop) {
                        emit_instr(INSTR_FINALLY);
                }

                if (state.each_loop) {
                        emit_instr(INSTR_POP);
                        emit_instr(INSTR_POP);
                }

                want_result = false;

                if (s->expression != NULL) {
                        emit_expression(s->expression);
                        if (!state.loop_want_result)
                                emit_instr(INSTR_POP);
                } else if (state.loop_want_result) {
                        emit_instr(INSTR_NIL);
                }

                emit_instr(INSTR_JUMP);
                vec_push(state.breaks, state.code.count);
                emit_int(0);
                break;
        case STATEMENT_CONTINUE:
                if (state.loop == 0)
                        fail("invalid continue statement (not inside a loop)");
                if (state.try > state.loop)
                        emit_instr(INSTR_FINALLY);
                emit_instr(INSTR_JUMP);
                vec_push(state.continues, state.code.count);
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

        return returns;
}

static void
emit_new_globals(void)
{
        static int GlobalCount = 0;

        for (int i = GlobalCount; i < global->owned.count; ++i) {
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
                } else if (!s->macro) {
                        emit_instr(INSTR_NIL);
                        emit_instr(INSTR_TARGET_GLOBAL);
                        emit_int(s->i);
                        emit_instr(INSTR_ASSIGN);
                        emit_instr(INSTR_POP);
                }
        }

        GlobalCount = global->owned.count;
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
                sym->class = class_new(s->class.name);
                sym->cnst = true;
                s->class.symbol = sym->class;

                if (s->class.pub) {
                        vec_push(state.exports, s->class.name);
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

        for (size_t i = 0; false && p[i] != NULL; ++i) {
                if (p[i]->type == STATEMENT_FUNCTION_DEFINITION) {
                        //symbolize_lvalue(state.global, p[i]->target, true, p[i]->pub);
                        /*
                         * TODO: figure out why this was ever here
                         *
                         * p[i]->value->name = NULL;
                         */
                }
                declare_classes(p[i]);
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

        for (int i = 0; p[i] != NULL; ++i) {
                emit_statement(p[i], false);
        }

        emit_instr(INSTR_HALT);

        /*
         * Add all of the location information from this compliation unit to the global list.
         */
        //struct location end = { 0 };
        //add_location(end, end, state);
        patch_location_info();
        vec_push(location_lists, state.expression_locations);
}

void
import_module(struct statement const *s)
{
        char const *name = s->import.module;
        char const *as = s->import.as;

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

        /*
         * If we've already generated code to load this module, we can skip to the part of the code
         * where we add the module to the current scope.
         */
        if (module_scope != NULL)
                goto Import;

        char *source = slurp_module(name);

        /*
         * Save the current compiler state so we can restore it after compiling
         * this module.
         */
        struct state save = state;
        state = freshstate();
        state.filename = name;

        compile(source);

        module_scope = state.global;

        /*
         * Mark it as external so that only public symbols can be used by other modules.
         */
        module_scope->external = true;

        struct module m = {
                .path = name,
                .code = state.code.items,
                .scope = module_scope
        };

        vec_push(modules, m);

        state = save;

        //emit_instr(INSTR_EXEC_CODE);
        //emit_symbol((uintptr_t) m.code);
        vm_exec(m.code);

Import:
{
        char const **identifiers = (char const **) s->import.identifiers.items;
        int n = s->import.identifiers.count;
        bool everything = n == 1 && strcmp(identifiers[0], "..") == 0;

        if (everything) {
                char const *id = scope_copy_public(state.global, module_scope);
                if (id != NULL)
                        fail("module '%s' exports conflcting name '%s'", name, id);
        } else for (int i = 0; i < n; ++i) {
                struct symbol *s = scope_lookup(module_scope, identifiers[i]);
                if (s == NULL || !s->public)
                        fail("module '%s' does not export '%s'", name, identifiers[i]);
                if (scope_lookup(state.global, identifiers[i]) != NULL)
                        fail("module '%s' exports conflicting name '%s'", name, identifiers[i]);
                scope_insert(state.global, s);
        }

        vec_push(state.imports, ((struct import){ .name = as, .scope = module_scope }));
}
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
        global->function = global;
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

        state.global = scope_new(state.global, false);

        vec_empty(state.imports);

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
                        s = scope_new(NULL, false);
                        vec_push(modules, ((struct module){
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
                        s = scope_new(NULL, false);
                        vec_push(modules, ((struct module){
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

        return state.code.items;
}

int
compiler_symbol_count(void)
{
        return scope_get_symbol();
}

char const *
compiler_get_location(char const *code, struct location *start, struct location *end)
{
        location_vector *locs = NULL;

        //printf("Looking for %zu\n", (size_t)(code - state.code.items));
        uintptr_t c = (uintptr_t) code;

        /*
         * First do a linear search for the group of locations which
         * contains this one.
         */
        for (int i = 0; i < location_lists.count; ++i) {
                if (location_lists.items[i].count == 0)
                        continue;
                if (c < location_lists.items[i].items[0].p_start)
                        continue;
                if (c > vec_last(location_lists.items[i])->p_end)
                        continue;
                locs = &location_lists.items[i];
                break;
        }

        if (locs == NULL) {
                *start = (struct location) { -1, -1 };
                return NULL;
        }

        /*
         * Now do a binary search within this group of locations.
         */
        int lo = 0,
            hi = locs->count - 1;

        while (lo <= hi) {
                int m = (lo / 2) + (hi / 2) + (lo & hi & 1);
                if      (c < locs->items[m].p_end) hi = m - 1;
                else if (c > locs->items[m].p_end) lo = m + 1;
                else {
                        lo = m;
                        break;
                }
        }

//        printf("Initially: (%zu, %zu)\n",
//               (size_t)(locs->items[lo].p_start - (uintptr_t)state.code.items),
//               (size_t)(locs->items[lo].p_end - (uintptr_t)state.code.items));

        if (c < locs->items[lo].p_start) {
                for (int i = lo + 1; i < locs->count; ++i) {
//                printf("Checking: (%zu, %zu)\n",
//                       (size_t)(locs->items[i].p_start - (uintptr_t)state.code.items),
//                       (size_t)(locs->items[i].p_end - (uintptr_t)state.code.items));
                        if (locs->items[i].p_start <= c && locs->items[i].p_end >= c) {
                                lo = i;
                                break;
                        }
                }
        }

        while (lo + 1 < locs->count && locs->items[lo + 1].p_start <= c &&
                        locs->items[lo + 1].p_end == locs->items[lo].p_end) {
                lo += 1;
        }

        *start = locs->items[lo].start;
        *end = locs->items[lo].end;

//        printf("Found: (%zu, %zu)\n",
//               (size_t)(locs->items[lo].p_start - (uintptr_t)state.code.items),
//               (size_t)(locs->items[lo].p_end - (uintptr_t)state.code.items));

        return locs->items[lo].filename;
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

inline static char *
mkcstr(struct value const *v)
{
        char *s = gc_alloc(v->bytes + 1);

        memcpy(s, v->string, v->bytes);
        s[v->bytes] = '\0';

        return s;
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

        vec_push(vs, v);

        while (next.type != VALUE_NONE) {
                vec_push(vs, next);
                next = va_arg(ap, struct value);
        }

        v = value_tuple(vs.count);
        for (int i = 0; i < vs.count; ++i) {
                v.items[i] = vs.items[i];
        }

TagAndReturn:
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(0, tag);
        return v;
}

struct value
tyexpr(struct expression const *e)
{
        struct value v;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                v = value_named_tuple(
                        "name", STRING_CLONE(e->identifier, strlen(e->identifier)),
                        "module", (e->module == NULL) ? NIL : STRING_CLONE(e->module, strlen(e->module)),
                        NULL
                );
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyId);
                break;
        case EXPRESSION_ARRAY:
                v = ARRAY(value_array_new());
                NOGC(v.array);
                for (int i = 0; i < e->elements.count; ++i) {
                        value_array_push(
                                v.array,
                                tagged(
                                        TyArrayItem,
                                        value_named_tuple(
                                                "item", tyexpr(e->elements.items[i]),
                                                "cond", (e->aconds.items[i] == NULL) ? NIL : tyexpr(e->aconds.items[i]),
                                                "optional", BOOLEAN(e->optional.items[i]),
                                                NULL
                                        ),
                                        NONE
                                )
                        );
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
        case EXPRESSION_FUNCTION:
                v = value_named_tuple(
                        "name", e->name != NULL ? STRING_CLONE(e->name, strlen(e->name)) : NIL,
                        "params", ARRAY(value_array_new()),
                        "rt", e->return_type != NULL ? tyexpr(e->return_type) : NIL,
                        "body", tystmt(e->body),
                        NULL
                );
                for (int i = 0; i < e->params.count; ++i) {
                        struct value name = STRING_CLONE(e->params.items[i], strlen(e->params.items[i]));
                        if (i == e->rest) {
                                value_array_push(
                                        v.items[1].array,
                                        tagged(TyGather, name, NONE)
                                );
                        } else if (i == e->ikwargs) {
                                value_array_push(
                                        v.items[1].array,
                                        tagged(TyKwargs, name, NONE)
                                );
                        } else {
                                struct value p = value_named_tuple(
                                        "name", name,
                                        "constraint", e->constraints.items[i] != NULL ? tyexpr(e->constraints.items[i]) : NIL,
                                        "default", e->dflts.items[i] != NULL ? tyexpr(e->dflts.items[i]) : NIL,
                                        NULL
                                );
                                value_array_push(v.items[1].array, tagged(TyParam, p, NONE));
                        }
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyFunc);
                break;
        case EXPRESSION_TUPLE:
                v = ARRAY(value_array_new());
                NOGC(v.array);
                for (int i = 0; i < e->es.count; ++i) {
                        value_array_push(
                                v.array,
                                tagged(
                                        TyRecordEntry,
                                        value_named_tuple(
                                                "item", tyexpr(e->es.items[i]),
                                                "name", (e->names.items[i] == NULL) ? NIL : STRING_CLONE(e->names.items[i], strlen(e->names.items[i])),
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
                v = value_tuple(2);
                v.items[0] = tyexpr(e->object);
                v.items[1] = STRING_CLONE(e->member_name, strlen(e->member_name));
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyMemberAccess);
                break;
        case EXPRESSION_WITH:
                v = tagged(
                        TyWith,
                        tystmt(e->with.let),
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
        case EXPRESSION_EQ:
                v = tagged(TyAssign, tyexpr(e->target), tyexpr(e->value), NONE);
                break;
        case EXPRESSION_GT:
                v = tagged(TyGT, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_LT:
                v = tagged(TyLT, tyexpr(e->left), tyexpr(e->right), NONE);
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
        case EXPRESSION_IN:
                v = tagged(TyIn, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_NOT_IN:
                v = tagged(TyNotIn, tyexpr(e->left), tyexpr(e->right), NONE);
                break;
        case EXPRESSION_STATEMENT:
                return tystmt(e->statement);
        default:
                v = tagged(TyExpr, PTR((void *)e), NONE);
        }

        return v;
}

struct value
tystmt(struct statement *s)
{
        struct value v;

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
                        NULL
                );
                for (int i = 0; i < s->class.methods.count; ++i) {
                        value_array_push(v.items[2].array, tyexpr(s->class.methods.items[i]));
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyClass);
                break;
        case STATEMENT_MATCH:
                v = value_tuple(2);
                v.items[0] = tyexpr(s->match.e);
                v.items[1] = ARRAY(value_array_new());
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        struct value _case = value_tuple(2);
                        _case.items[0] = tyexpr(s->match.patterns.items[i]);
                        _case.items[1] = tystmt(s->match.statements.items[i]);
                        value_array_push(
                                v.items[1].array,
                                _case
                        );
                }
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, TyMatch);
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
        case STATEMENT_IF:
                v = value_tuple(3);
                v.items[0] = ARRAY(value_array_new());
                for (int i = 0; i < s->iff.parts.count; ++i) {
                        struct condpart *part = s->iff.parts.items[i];
                        if (part->target != NULL) {
                                value_array_push(
                                        v.items[0].array,
                                        tagged(
                                                part->def ? TyLet : TyAssign,
                                                tyexpr(part->target),
                                                tyexpr(part->e),
                                                NONE
                                        )
                                );
                        } else {
                                value_array_push(v.items[0].array, tyexpr(part->e));
                        }
                }
                v.items[1] = tystmt(s->iff.then);
                v.items[2] = s->iff.otherwise != NULL ? tystmt(s->iff.otherwise) : NIL;
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(0, s->iff.neg ? TyIfNot : TyIf);
                break;
        case STATEMENT_FUNCTION_DEFINITION:
                v = tyexpr(s->value);
                v.tags = tags_push(0, TyFuncDef);
                break;
        case STATEMENT_NULL:
                v = TAG(TyNull);
                break;
        case STATEMENT_EXPRESSION:
                return tyexpr(s->expression);
        default:
                v = tagged(TyStmt, PTR((void *)s), NONE);
        }

        return v;
}

struct statement *
cstmt(struct value *v)
{
        struct statement *s = gc_alloc(sizeof *s);
        *s = (struct statement){0};

        s->start = s->end = Nowhere;

        if (tags_first(v->tags) == TyStmt) {
                return v->ptr;
        } else if (tags_first(v->tags) == TyLet) {
                struct value *pub = tuple_get(v, "public");
                s->type = STATEMENT_DEFINITION;
                s->pub = pub != NULL && value_truthy(pub);
                s->target = cexpr(&v->items[0]);
                s->value = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyFuncDef) {
                struct value f = *v;
                f.tags = tags_push(0, TyFunc);
                s->type = STATEMENT_FUNCTION_DEFINITION;
                s->value = cexpr(&f);
                s->target = gc_alloc(sizeof *s->target);
                s->target->type = EXPRESSION_IDENTIFIER;
                s->target->identifier = mkcstr(tuple_get(v, "name"));
                s->target->module = NULL;
                s->target->constraint = NULL;
        } else if (tags_first(v->tags) == TyClass) {
                s->type = STATEMENT_CLASS_DEFINITION;
                s->class.name = mkcstr(tuple_get(v, "name"));
                struct value *super = tuple_get(v, "super");
                s->class.super = (super != NULL && super->type != VALUE_NIL) ? cexpr(super) : NULL;
                struct value *methods = tuple_get(v, "methods");
                vec_init(s->class.methods);
                for (int i = 0; i < methods->array->count; ++i) {
                        vec_push(s->class.methods, cexpr(&methods->array->items[i]));
                }
        } else if (tags_first(v->tags) == TyIf ||
                   tags_first(v->tags) == TyIfNot) {
                s->type = STATEMENT_IF;
                s->iff.neg = tags_first(v->tags) == TyIfNot;
                vec_init(s->iff.parts);

                struct value *parts = &v->items[0];
                for (int i = 0; i < parts->array->count; ++i) {
                        struct value *part = &parts->array->items[i];
                        struct condpart *cp = gc_alloc(sizeof *cp);
                        if (tags_first(part->tags) == TyLet) {
                                cp->def = true;
                                cp->target = cexpr(&part->items[0]);
                                cp->e = cexpr(&part->items[1]);
                        } else if (tags_first(part->tags) == TyAssign) {
                                cp->def = false;
                                cp->target = cexpr(&part->items[0]);
                                cp->e = cexpr(&part->items[1]);
                        } else {
                                cp->def = false;
                                cp->target = NULL;
                                cp->e = cexpr(part);
                        }
                        vec_push(s->iff.parts, cp);
                }
                s->iff.then = cstmt(&v->items[1]);
                if (v->count > 2 && v->items[2].type != VALUE_NIL) {
                        s->iff.otherwise = cstmt(&v->items[2]);
                } else {
                        s->iff.otherwise = NULL;
                }
        } else if (tags_first(v->tags) == TyMatch) {
                s->type = STATEMENT_MATCH;
                s->match.e = cexpr(&v->items[0]);
                vec_init(s->match.patterns);
                vec_init(s->match.statements);
                vec_init(s->match.conds);
                struct value *cases = &v->items[1];
                for (int i = 0; i < cases->array->count; ++i) {
                        struct value *_case = &cases->array->items[i];
                        vec_push(s->match.patterns, cexpr(&_case->items[0]));
                        vec_push(s->match.statements, cstmt(&_case->items[1]));
                        vec_push(s->match.conds, NULL);
                }
        } else if (tags_first(v->tags) == TyReturn) {
                s->type = STATEMENT_RETURN;
                vec_init(s->returns);
                if (v->type == VALUE_TUPLE) {
                        for (int i = 0; i < v->count; ++i) {
                                vec_push(s->returns, cexpr(&v->items[i]));
                        }
                } else {
                        v->tags = tags_pop(v->tags);
                        vec_push(s->returns, cexpr(v));
                }
        } else if (tags_first(v->tags) == TyBlock) {
                s->type = STATEMENT_BLOCK;
                vec_init(s->statements);
                for (int i = 0; i < v->array->count; ++i) {
                        vec_push(s->statements, cstmt(&v->array->items[i]));
                }
        } else if (tags_first(v->tags) == TyMulti) {
                s->type = STATEMENT_MULTI;
                vec_init(s->statements);
                for (int i = 0; i < v->array->count; ++i) {
                        vec_push(s->statements, cstmt(&v->array->items[i]));
                }
        } else if (v->type == VALUE_TAG && v->tag == TyNull) {
                s->type = STATEMENT_NULL;
        } else {
                s->type = STATEMENT_EXPRESSION;
                s->expression = cexpr(v);
        }

        return s;
}

struct expression *
cexpr(struct value *v)
{
        struct expression *e = gc_alloc(sizeof *e);
        *e = (struct expression){0};

        e->start = e->end = Nowhere;

        if (tags_first(v->tags) == TyExpr) {
                return v->ptr;
        } else if (tags_first(v->tags) == TyValue) {
                struct value *value = gc_alloc(sizeof *value);
                *value = *v;
                value->tags = tags_pop(value->tags);
                if (value->tags == 0) {
                        value->type &= ~VALUE_TAGGED;
                }
                e->type = EXPRESSION_VALUE;
                e->v = value;
                gc_push(value);
        } else if (tags_first(v->tags) == TyInt) {
                e->type = EXPRESSION_INTEGER;
                e->integer = v->integer;
        } else if (tags_first(v->tags) == TyId) {
                e->type = EXPRESSION_IDENTIFIER;
                e->identifier = mkcstr(tuple_get(v, "name"));
                struct value *mod = tuple_get(v, "module");
                e->module = (mod != NULL && mod->type != VALUE_NIL) ? mkcstr(mod) : NULL;
        } else if (tags_first(v->tags) == TySpread) {
                struct value v_ = *v;
                v_.tags = tags_pop(v_.tags);
                e->type = EXPRESSION_SPREAD;
                e->value = cexpr(&v_);
        } else if (tags_first(v->tags) == TyString) {
                e->type = EXPRESSION_STRING;
                e->string = mkcstr(v);
        } else if (tags_first(v->tags) == TyArray) {
                e->type = EXPRESSION_ARRAY;
                vec_init(e->elements);
                vec_init(e->aconds);
                vec_init(e->optional);
                for (int i = 0; i < v->array->count; ++i) {
                        struct value *entry = &v->array->items[i];
                        struct value *optional = tuple_get(entry, "optional");
                        struct value *cond = tuple_get(entry, "cond");
                        vec_push(e->elements, cexpr(tuple_get(entry, "item")));
                        vec_push(e->optional, optional != NULL ? optional->boolean : false);
                        vec_push(e->aconds, (cond != NULL && cond->type != VALUE_NIL) ? cexpr(cond) : NULL);
                }
        } else if (tags_first(v->tags) == TyRecord) {
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
                        vec_push(e->es, cexpr(item));
                        vec_push(e->names, name != NULL && name->type != VALUE_NIL ? mkcstr(name) : NULL);
                        vec_push(e->required, optional != NULL ? !optional->boolean : true);
                        vec_push(e->tconds, cond != NULL && cond->type != VALUE_NIL ? cexpr(cond) : NULL);
                }
        } else if (tags_first(v->tags) == TyDict) {
                e->type = EXPRESSION_DICT;
                e->dtmp = NULL;
                vec_init(e->keys);
                vec_init(e->values);

                struct value *items = tuple_get(v, "items");
                struct value *dflt = tuple_get(v, "default");

                e->dflt = dflt != NULL ? cexpr(dflt) : NULL;

                for (int i = 0; i < items->array->count; ++i) {
                        vec_push(e->keys, cexpr(&items->array->items[i].items[0]));
                        vec_push(e->values, cexpr(&items->array->items[i].items[1]));
                }
        } else if (tags_first(v->tags) == TyCall) {
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
                                vec_push(e->args, cexpr(tuple_get(arg, "arg")));
                                vec_push(e->fconds, cond != NULL ? cexpr(cond) : NULL);
                        } else {
                                vec_push(e->kwargs, cexpr(tuple_get(arg, "arg")));
                                vec_push(e->kws, mkcstr(name));
                                vec_push(e->fkwconds, cond != NULL ? cexpr(cond) : NULL);
                        }
                }
        } else if (tags_first(v->tags) == TyMethodCall) {
                e->type = EXPRESSION_METHOD_CALL;
                vec_init(e->method_args);
                vec_init(e->method_kws);
                vec_init(e->method_kwargs);
                vec_init(e->mconds);

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
                                vec_push(e->method_args, cexpr(tuple_get(arg, "arg")));
                                vec_push(e->mconds, cond != NULL ? cexpr(cond) : NULL);
                        } else {
                                vec_push(e->method_kwargs, cexpr(tuple_get(arg, "arg")));
                                vec_push(e->method_kws, mkcstr(name));
                        }
                }
        } else if (tags_first(v->tags) == TyFunc || tags_first(v->tags) == TyImplicitFunc) {
                e->type = tags_first(v->tags) == TyFunc ? EXPRESSION_FUNCTION : EXPRESSION_IMPLICIT_FUNCTION;
                e->ikwargs = -1;
                e->rest = -1;
                e->ftype = FT_NONE;
                struct value *name = tuple_get(v, "name");
                struct value *params = tuple_get(v, "params");
                struct value *rt = tuple_get(v, "rt");
                e->name = (name != NULL && name->type != VALUE_NIL) ? mkcstr(name) : NULL;
                e->return_type = (rt != NULL && rt->type != VALUE_NIL) ? cexpr(rt) : NULL;
                vec_init(e->params);
                vec_init(e->constraints);
                vec_init(e->dflts);
                for (int i = 0; i < params->array->count; ++i) {
                        struct value *p = &params->array->items[i];
                        if (tags_first(p->tags) == TyParam) {
                                vec_push(e->params, mkcstr(tuple_get(p, "name")));
                                struct value *c = tuple_get(p, "constraint");
                                struct value *d = tuple_get(p, "default");
                                vec_push(e->constraints, (c != NULL && c->type != VALUE_NIL) ? cexpr(c) : NULL);
                                vec_push(e->dflts, (d != NULL && d->type != VALUE_NIL) ? cexpr(d) : NULL);
                        } else if (tags_first(p->tags) == TyGather) {
                                vec_push(e->params, mkcstr(p));
                                vec_push(e->constraints, NULL);
                                vec_push(e->dflts, NULL);
                                e->rest = i;
                        } else if (tags_first(p->tags) == TyKwargs) {
                                vec_push(e->params, mkcstr(p));
                                vec_push(e->constraints, NULL);
                                vec_push(e->dflts, NULL);
                                e->ikwargs = i;
                        }
                }
                e->body = cstmt(tuple_get(v, "body"));
        } else if (tags_first(v->tags) == TyMemberAccess) {
                e->type = EXPRESSION_MEMBER_ACCESS;
                e->object = cexpr(&v->items[0]);
                e->member_name = mkcstr(&v->items[1]);
        } else if (tags_first(v->tags) == TyWith) {
                make_with(e, cstmt(&v->items[0]), cstmt(&v->items[1]));
        } else if (tags_first(v->tags) == TyCond) {
                e->type = EXPRESSION_CONDITIONAL;
                e->cond = cexpr(&v->items[0]);
                e->then = cexpr(&v->items[1]);
                e->otherwise = cexpr(&v->items[2]);
        } else if (v->type == VALUE_TAG && v->tag == TyNil) {
                e->type = EXPRESSION_NIL;
        } else if (tags_first(v->tags) == TyBool) {
                e->type = EXPRESSION_BOOLEAN;
                e->boolean = v->boolean;
        } else if (tags_first(v->tags) == TyAssign) {
                e->type = EXPRESSION_EQ;
                e->target = cexpr(&v->items[0]);
                e->value = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyWtf) {
                e->type = EXPRESSION_WTF;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyAdd) {
                e->type = EXPRESSION_PLUS;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TySub) {
                e->type = EXPRESSION_MINUS;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyMod) {
                e->type = EXPRESSION_PERCENT;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyDiv) {
                e->type = EXPRESSION_DIV;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyMul) {
                e->type = EXPRESSION_STAR;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyEq) {
                e->type = EXPRESSION_DBL_EQ;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyNotEq) {
                e->type = EXPRESSION_NOT_EQ;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyIn) {
                e->type = EXPRESSION_IN;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyNotIn) {
                e->type = EXPRESSION_NOT_IN;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyOr) {
                e->type = EXPRESSION_OR;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyAnd) {
                e->type = EXPRESSION_AND;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyUserOp) {
                e->type = EXPRESSION_USER_OP;
                e->left = cexpr(&v->items[0]);
                e->right = cexpr(&v->items[1]);
        } else if (tags_first(v->tags) == TyLet) {
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(v);
        } else if (tags_first(v->tags) == TyMatch) {
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(v);
        } else if (tags_first(v->tags) == TyStmt) {
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(v);
        } else if (tags_first(v->tags) == TyBlock) {
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(v);
        } else if (v->type == VALUE_TAG && v->tag == TyNull) {
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(v);
        } else if (tags_first(v->tags) == TyMulti) {
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(v);
        } else if (tags_first(v->tags) == TyFuncDef) {
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(v);
        } else if (tags_first(v->tags) == TyClass) {
                e->type = EXPRESSION_STATEMENT;
                e->statement = cstmt(v);
        } else {
                fail("invalid value passed to cexpr(): %s", value_show(v));
        }

        return e;
}

struct value
tyeval(struct expression *e)
{
        symbolize_expression(state.macro_scope, e);

        byte_vector code_save = state.code;
        vec_init(state.code);

        emit_expression(e);
        emit_instr(INSTR_HALT);

        vm_exec(state.code.items);

        struct value v = *vm_get(0);
        vm_pop();

        state.code = code_save;

        return v;
}

struct expression *
typarse(struct expression *e)
{
        symbolize_expression(state.global, e);

        byte_vector code_save = state.code;
        vec_init(state.code);

        emit_expression(e);
        emit_instr(INSTR_HALT);

        vm_exec(state.code.items);
        state.code = code_save;

        struct value m = *vm_get(0);
        vm_pop();

        struct scope *macro_scope_save = state.macro_scope;
        state.macro_scope = state.global;

        struct value expr = vm_call(&m, 0);

        state.macro_scope = macro_scope_save;

        return cexpr(&expr);
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
        sym->class = class_new(s->class.name);
        sym->cnst = true;
        s->class.symbol = sym->class;

        if (s->class.pub) {
                vec_push(state.exports, s->class.name);
        }
}

void
define_function(struct statement *s)
{
        symbolize_lvalue(state.global, s->target, true, s->pub);
}

void
define_macro(struct statement *s)
{
        symbolize_statement(state.global, s);
        s->target->symbol->macro = true;

        s->type = STATEMENT_FUNCTION_DEFINITION;

        byte_vector code_save = state.code;
        vec_init(state.code);

        emit_statement(s, false);

        emit_instr(INSTR_HALT);

        vm_exec(state.code.items);

        state.code = code_save;
}

bool
is_macro(struct expression const *e)
{
        struct symbol *s = NULL;

        assert(e->type == EXPRESSION_IDENTIFIER);

        if (e->module == NULL) {
                s = scope_lookup(state.global, e->identifier);
        } else {
                struct scope *mod = search_import_scope(e->module);
                if (mod != NULL) {
                        s = scope_lookup(mod, e->identifier);
                }
        }

        return s != NULL && s->macro;
}

void
compiler_symbolize_expression(struct expression *e)
{
        symbolize_expression(state.global, e);
        e->type |= EXPRESSION_SYMBOLIZED;
}
