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

#define EXPR(...) ((struct expression){ .loc = { -1, -1 }, __VA_ARGS__ })

struct eloc {
        union {
                uintptr_t p;
                size_t offset;
        };
        struct location loc;
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
typedef vec(struct reference) reference_vector;
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

        symbol_vector bound_symbols;
        reference_vector refs;

        int_vector check;
        struct scope *check_scope;
        
        offset_vector breaks;
        offset_vector continues;
        offset_vector match_fails;
        offset_vector match_successes;

        int function_depth;
        bool each_loop;

        uint64_t try;
        uint64_t loop;

        import_vector imports;
        vec(char *) exports;

        struct scope *global;

        char const *filename;
        struct location loc;

        location_vector expression_locations;
};

static jmp_buf jb;
static char const *err_msg;
static char err_buf[512];

static int builtin_modules;
static int builtin_count;

static int jumpdistance;
static vec(struct module) modules;
static struct state state;

static vec(location_vector) location_lists;

static struct scope *global;
static int global_count;

static uint64_t t;

static void
symbolize_statement(struct scope *scope, struct statement *s);

static void
symbolize_pattern(struct scope *scope, struct expression *e);

static void
symbolize_expression(struct scope *scope, struct expression *e);

static void
emit_statement(struct statement const *s);

static void
emit_expression(struct expression const *e);

static void
emit_assignment(struct expression *target, struct expression const *e);

static void
emit_case(struct expression const *pattern, struct expression const *condition, struct statement const *s);

static struct scope *
get_import_scope(char const *);

static void
import_module(struct statement const *s);

static void
compile(char const *source);

noreturn static void
fail(char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        int n;
        if (state.filename == NULL)
                n = sprintf(err_buf, "CompileError: %d:%d: ", state.loc.line + 1,state.loc.col + 1);
        else
                n = sprintf(err_buf, "CompileError: %s:%d:%d: ", state.filename, state.loc.line + 1,state.loc.col + 1);

        vsnprintf(err_buf + n, sizeof err_buf - n, fmt, ap);
        err_msg = err_buf;

        LOG("Failing with error: %s", err_buf);

        va_end(ap);

        longjmp(jb, 1);
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
        if (source == NULL)
                fail("failed to read file: %s", pathbuf);

        return source;
}

static void
add_location(struct location loc)
{
        if (loc.line == -1 && loc.col == -1)
                return;

        vec_push(
                state.expression_locations,
                ((struct eloc) {
                        .offset = state.code.count,
                        .loc = loc,
                        .filename = state.filename
                })
        );
}

static void
patch_location_info(void)
{
        struct eloc *locs = state.expression_locations.items;
        for (int i = 0; i < state.expression_locations.count; ++i)
                locs[i].p = (uintptr_t)(state.code.items + locs[i].offset);
}

inline static void
addref(int symbol)
{
        LOG("adding reference: %d", symbol);

        struct reference r = {
                .symbol = symbol,
                .offset = state.code.count
        };

        vec_push(state.refs, r);
}

inline static struct symbol *
addsymbol(struct scope *scope, char const *name)
{
        assert(name != NULL);

        if (scope_locally_defined(scope, name) && strcmp(name, "_") != 0)
                fail("redeclaration of variable: %s", name);

        struct symbol *s = scope_add(scope, name);

        LOG("adding symbol: %s -> %d", name, s->symbol);

        return s;
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

inline static struct symbol *
getsymbol(struct scope const *scope, char const *name, bool *local)
{
        /*
         * _ can never be used as anything but an lvalue.
         */
        if (strcmp(name, "_") == 0)
                fail("the special identifier '_' can only be used as an lvalue");

        struct symbol *s = scope_lookup(scope, name);
        if (s == NULL)
                fail("reference to undefined variable: %s", name);

        if (s->scope->external && !s->public)
                fail("reference to non-public external variable '%s'", name);

        bool is_local = (s->scope->function == scope->function) || (s->scope == global) || (s->scope->parent == global);

        if (local != NULL)
                *local = is_local;

        if (!is_local && scope_is_subscope(s->scope, state.check_scope))
                vec_push(state.check, s->symbol);


        return s;
}

inline static struct symbol *
tmpsymbol(void)
{
        static int i;
        static char idbuf[8];

        assert(i <= 9999999);

        sprintf(idbuf, "%d", i++);

        if (scope_locally_defined(global, idbuf))
                return scope_lookup(global, idbuf);
        else
                return scope_add(global, sclone(idbuf));
}

static struct state
freshstate(void)
{
        struct state s;

        vec_init(s.code);

        vec_init(s.refs);
        vec_init(s.bound_symbols);

        vec_init(s.check);
        s.check_scope = NULL;

        vec_init(s.breaks);
        vec_init(s.continues);

        vec_init(s.imports);
        vec_init(s.exports);

        s.global = scope_new(global, false);

        s.function_depth = 0;
        s.each_loop = false;

        s.try = 0;
        s.loop = 0;

        s.filename = NULL;
        s.loc = (struct location){ 0, 0 };

        vec_init(s.expression_locations);

        return s;
}

inline static bool
is_loop(struct statement const *s)
{
        switch (s->type) {
        case STATEMENT_FOR_LOOP:
        case STATEMENT_WHILE_LOOP:
        case STATEMENT_WHILE_LET:
        case STATEMENT_EACH_LOOP:
        case STATEMENT_WHILE_MATCH:
                return true;
        default:
                return false;
        }
}

static struct scope *
get_import_scope(char const *name)
{
        for (int i = 0; i < state.imports.count; ++i)
                if (strcmp(name, state.imports.items[i].name) == 0)
                        return state.imports.items[i].scope;

        fail("reference to undefined module: %s", name);
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

                symbolize_expression(scope, ms[i]);
                ms[i]->is_method = true;

                ms[i]->name = name;
        }
}

static void
try_symbolize_application(struct scope *scope, struct expression *e)
{
        if (e->type == EXPRESSION_FUNCTION_CALL && e->function->type == EXPRESSION_IDENTIFIER) {
                symbolize_expression(scope, e->function);
                if (e->function->symbol->tag != -1) {
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
                                struct expression *items = alloc(sizeof *items);
                                items->type = EXPRESSION_ARRAY;
                                vec_init(items->elements);
                                for (int i = 0; i < tagc; ++i)
                                        vec_push(items->elements, tagged[i]);
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
symbolize_lvalue(struct scope *scope, struct expression *target, bool decl)
{
        state.loc = target->loc;

        try_symbolize_application(scope, target);

        switch (target->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
                if (decl) {
                        target->symbol = addsymbol(scope, target->identifier);
                        target->local = true;
                } else {
                        target->symbol = getsymbol(scope, target->identifier, &target->local);
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_lvalue(scope, target->tagged, decl);
                target->symbol = getsymbol(
                        ((target->module == NULL || *target->module == '\0') ? state.global : get_import_scope(target->module)),
                        target->identifier,
                        NULL
                );
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < target->elements.count; ++i)
                        symbolize_lvalue(scope, target->elements.items[i], decl);
                break;
        case EXPRESSION_SUBSCRIPT:
                symbolize_expression(scope, target->container);
                symbolize_expression(scope, target->subscript);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                symbolize_expression(scope, target->object);
                break;
        }
}

static void
symbolize_pattern(struct scope *scope, struct expression *e)
{
        if (e == NULL)
                return;

        try_symbolize_application(scope, e);

        if (e->type == EXPRESSION_IDENTIFIER && is_tag(e))
                goto tag;

        state.loc = e->loc;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (scope_locally_defined(scope, e->identifier) || e->module != NULL) {
                        e->type = EXPRESSION_MUST_EQUAL;
                        struct scope *s = (e->module == NULL || *e->module == '\0') ? scope : get_import_scope(e->module);
                        e->symbol = getsymbol(s, e->identifier, NULL);
                } else {
        case EXPRESSION_MATCH_NOT_NIL:
                        e->symbol = addsymbol(scope, e->identifier);
                }
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < e->elements.count; ++i)
                        symbolize_pattern(scope, e->elements.items[i]);
                break;
        case EXPRESSION_VIEW_PATTERN:
                symbolize_expression(scope, e->left);
                symbolize_pattern(scope, e->right);
                break;
        case EXPRESSION_MATCH_REST:
                e->symbol = addsymbol(scope, e->identifier);
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_pattern(scope, e->tagged);
                break;
        tag:
                symbolize_expression(scope, e);
                e->type = EXPRESSION_MUST_EQUAL;
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

        state.loc = e->loc;

        struct scope *subscope;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                LOG("symbolizing var: %s%s%s", (e->module == NULL ? "" : e->module), (e->module == NULL ? "" : "::"), e->identifier);
                e->symbol = getsymbol(
                        ((e->module == NULL || *e->module == '\0') ? scope : get_import_scope(e->module)),
                        e->identifier,
                        &e->local
                );
                LOG("var %s local", e->local ? "is" : "is NOT");
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
                        symbolize_pattern(subscope, e->patterns.items[i]);
                        symbolize_expression(subscope, e->conds.items[i]);
                        symbolize_expression(subscope, e->thens.items[i]);
                }
                break;
        case EXPRESSION_PLUS:
        case EXPRESSION_MINUS:
        case EXPRESSION_STAR:
        case EXPRESSION_DIV:
        case EXPRESSION_PERCENT:
        case EXPRESSION_AND:
        case EXPRESSION_OR:
        case EXPRESSION_LT:
        case EXPRESSION_LEQ:
        case EXPRESSION_GT:
        case EXPRESSION_GEQ:
        case EXPRESSION_DBL_EQ:
        case EXPRESSION_NOT_EQ:
        case EXPRESSION_DOT_DOT:
                symbolize_expression(scope, e->left);
                symbolize_expression(scope, e->right);
                break;
        case EXPRESSION_PREFIX_BANG:
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
        case EXPRESSION_FUNCTION_CALL:
                symbolize_expression(scope, e->function);
                for (size_t i = 0;  i < e->args.count; ++i)
                        symbolize_expression(scope, e->args.items[i]);
                break;
        case EXPRESSION_SUBSCRIPT:
                symbolize_expression(scope, e->container);
                symbolize_expression(scope, e->subscript);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                symbolize_expression(scope, e->object);
                break;
        case EXPRESSION_METHOD_CALL:
                symbolize_expression(scope, e->object);
                for (size_t i = 0;  i < e->method_args.count; ++i)
                        symbolize_expression(scope, e->method_args.items[i]);
                break;
        case EXPRESSION_EQ:
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MINUS_EQ:
                symbolize_expression(scope, e->value);
                symbolize_lvalue(scope, e->target, false);
                break;
        case EXPRESSION_FUNCTION:

                e->is_method = false;

                if (e->name != NULL) {
                        scope = scope_new(scope, false);
                        e->function_symbol = addsymbol(scope, e->name);
                } else {
                        e->function_symbol = NULL;
                }

                scope = scope_new(scope, true);

                vec_init(e->param_symbols);
                for (size_t i = 0; i < e->params.count; ++i)
                        vec_push(e->param_symbols, addsymbol(scope, e->params.items[i]));
                symbolize_statement(scope, e->body);

                e->bound_symbols.items = scope->function_symbols.items;
                e->bound_symbols.count = scope->function_symbols.count;

                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i)
                        symbolize_expression(scope, e->elements.items[i]);
                break;
        case EXPRESSION_DICT:
                for (size_t i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(scope, e->keys.items[i]);
                        symbolize_expression(scope, e->values.items[i]);
                }
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

        int_vector check_save = state.check;
        struct scope *check_scope_save = state.check_scope;

        if (is_loop(s)) {
                vec_init(state.check);
                state.check_scope = scope;
        }

        state.loc = s->loc;

        struct scope *subscope;
        struct symbol *sym;

        switch (s->type) {
        case STATEMENT_IMPORT:
                import_module(s);
                break;
        case STATEMENT_EXPORT:
                vec_push_n(state.exports, s->exports.items, s->exports.count);
                break;
        case STATEMENT_EXPRESSION:
                symbolize_expression(scope, s->expression);
                break;
        case STATEMENT_CLASS_DEFINITION:
                if (scope_locally_defined(state.global, s->class.name))
                        fail("redeclaration of class: %s", s->class.name);
                if (s->class.super != NULL) {
                        symbolize_expression(scope, s->class.super);
                        if (!is_class(s->class.super))
                                fail("attempt to extend non-class");
                }
                sym = scope_add(state.global, s->class.name);
                sym->class = class_new(s->class.name);
                s->class.symbol = sym->class;
                symbolize_methods(scope, s->class.methods.items, s->class.methods.count);
                break;
        case STATEMENT_TAG_DEFINITION:
                if (scope_locally_defined(state.global, s->tag.name))
                        fail("redeclaration of tag: %s", s->tag.name);
                if (s->tag.super != NULL) {
                        symbolize_expression(scope, s->tag.super);
                        if (!is_tag(s->tag.super))
                                fail("attempt to extend non-tag");
                }
                sym = scope_add(state.global, s->tag.name);
                sym->tag = tags_new(s->tag.name);
                s->tag.symbol = sym->tag;
                symbolize_methods(scope, s->tag.methods.items, s->tag.methods.count);
                break;
        case STATEMENT_BLOCK:
                scope = scope_new(scope, false);
                for (size_t i = 0; i < s->statements.count; ++i)
                        symbolize_statement(scope, s->statements.items[i]);
                break;
        case STATEMENT_THROW:
                symbolize_expression(scope, s->throw);
                break;
        case STATEMENT_TRY:
        {
                symbolize_statement(scope_new(scope, false), s->try.s);

                for (int i = 0; i < s->try.patterns.count; ++i) {
                        struct scope *catch = scope_new(scope, false);
                        symbolize_pattern(catch, s->try.patterns.items[i]);
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
                        symbolize_pattern(subscope, s->match.patterns.items[i]);
                        symbolize_expression(subscope, s->match.conds.items[i]);
                        symbolize_statement(subscope, s->match.statements.items[i]);
                }
                s->match.check = state.check;
                break;
        case STATEMENT_WHILE_LET:
                symbolize_expression(scope, s->while_let.e);
                subscope = scope_new(scope, false);
                symbolize_pattern(subscope, s->while_let.pattern);
                symbolize_statement(subscope, s->while_let.block);
                s->while_let.check = state.check;
                break;
        case STATEMENT_IF_LET:
                symbolize_expression(scope, s->if_let.e);
                subscope = scope_new(scope, false);
                symbolize_pattern(subscope, s->if_let.pattern);
                symbolize_statement(subscope, s->if_let.then);
                symbolize_statement(scope, s->if_let.otherwise); /* note that this is not done in the subscope */
                break;
        case STATEMENT_FOR_LOOP:
                scope = scope_new(scope, false);
                symbolize_statement(scope, s->for_loop.init);
                symbolize_expression(scope, s->for_loop.cond);
                symbolize_expression(scope, s->for_loop.next);
                symbolize_statement(scope, s->for_loop.body);
                s->for_loop.check = state.check;
                break;
        case STATEMENT_EACH_LOOP:
                scope = scope_new(scope, false);
                symbolize_lvalue(scope, s->each.target, true);
                symbolize_expression(scope, s->each.array);
                symbolize_statement(scope, s->each.body);
                s->each.check = state.check;
                break;
        case STATEMENT_WHILE_LOOP:
                scope = scope_new(scope, false);
                symbolize_expression(scope, s->while_loop.cond);
                symbolize_statement(scope, s->while_loop.body);
                s->while_loop.check = state.check;
                break;
        case STATEMENT_CONDITIONAL:
                symbolize_expression(scope, s->conditional.cond);
                symbolize_statement(scope, s->conditional.then_branch);
                symbolize_statement(scope, s->conditional.else_branch);
                break;
        case STATEMENT_RETURN:
                symbolize_expression(scope, s->return_value);
                break;
        case STATEMENT_DEFINITION:
                symbolize_expression(scope, s->value);
                symbolize_lvalue(scope, s->target, true);
                break;
        }

        if (is_loop(s)) {
                state.check_scope = check_scope_save;
                state.check = check_save;
        }
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

inline static void
_emit_instr(char c)
{
        vec_push(state.code, c);
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
emit_checks(int_vector check)
{
        emit_instr(INSTR_CHECK_VARS);
        emit_int(check.count);
        for (int i = 0; i < check.count; ++i)
                emit_symbol(check.items[i]);
}

static void
emit_function(struct expression const *e)
{
        assert(e->type == EXPRESSION_FUNCTION);
        
        /*
         * Save the current reference and bound-symbols vectors so we can
         * restore them after compiling the current function.
         */
        reference_vector refs_save = state.refs;
        symbol_vector syms_save = state.bound_symbols;
        vec_init(state.refs);
        state.bound_symbols.items = e->bound_symbols.items;
        state.bound_symbols.count = e->bound_symbols.count;
        ++state.function_depth;
        uint64_t loop_save = state.loop;
        uint64_t try_save = state.try;
        uint64_t each_loop_save = state.each_loop;
        state.loop = state.try = state.each_loop = 0;

        emit_int(e->param_symbols.count);
        emit_int(e->bound_symbols.count);

        while (((uintptr_t)(state.code.items + state.code.count)) % (_Alignof (int)) != ((_Alignof (int)) - 1))
                vec_push(state.code, 0x00);
        vec_push(state.code, 0xFF);

        for (int i = 0; i < e->bound_symbols.count; ++i)
                emit_int(e->bound_symbols.items[i]->symbol);

        /*
         * Write an int to the emitted code just to make some room.
         */
        size_t size_offset = state.code.count;
        emit_int(0);

        /*
         * Remember where in the code this function's code begins so that we can compute
         * the relative offset of references to non-local variables.
         */
        size_t start_offset = state.code.count;

        emit_statement(e->body);

        /*
         * Add an implicit 'return nil;' in case the function doesn't explicitly return in its body.
         */
        emit_statement(&(struct statement){ .type = STATEMENT_RETURN, .return_value = NULL, .loc = {42, 42} });

        int bytes = state.code.count - size_offset - sizeof (int);
        LOG("bytes in func = %d", bytes);
        memcpy(state.code.items + size_offset, &bytes, sizeof (int));

        emit_int(state.refs.count);
        for (int i = 0; i < state.refs.count; ++i) {
                emit_symbol(state.refs.items[i].symbol);
                emit_symbol(state.refs.items[i].offset - start_offset);
        }

        state.refs = refs_save;
        state.bound_symbols = syms_save;
        --state.function_depth;
        state.loop = loop_save;
        state.try = try_save;
        state.each_loop = each_loop_save;

        if (e->function_symbol != NULL) {
                emit_instr(INSTR_TARGET_VAR);
                emit_symbol(e->function_symbol->symbol);
                emit_instr(INSTR_ASSIGN);
        }
}

static void
emit_conditional_statement(struct statement const *s)
{
        emit_expression(s->conditional.cond);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF, size_t then_branch);

        if (s->conditional.else_branch != NULL)
                emit_statement(s->conditional.else_branch);

        PLACEHOLDER_JUMP(INSTR_JUMP, size_t end);

        PATCH_JUMP(then_branch);

        emit_statement(s->conditional.then_branch);

        PATCH_JUMP(end);
}

static void
emit_conditional_expression(struct expression const *e)
{
        emit_expression(e->cond);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t false_branch);

        emit_expression(e->then);

        PLACEHOLDER_JUMP(INSTR_JUMP, size_t end);

        PATCH_JUMP(false_branch);

        emit_expression(e->otherwise);

        PATCH_JUMP(end);
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
emit_special_string(struct expression const *e)
{
        emit_instr(INSTR_STRING);
        emit_string(e->strings.items[0]);

        for (int i = 0; i < e->expressions.count; ++i) {
                emit_expression(e->expressions.items[i]);
                emit_instr(INSTR_TO_STRING);
                emit_instr(INSTR_STRING);
                emit_string(e->strings.items[i + 1]);
        }

        emit_instr(INSTR_CONCAT_STRINGS);
        emit_int(2 * e->expressions.count + 1);
}

static void
emit_throw(struct statement const *s)
{
        emit_expression(s->throw);
        emit_instr(INSTR_THROW);
}

static void
emit_try(struct statement const *s)
{
        emit_instr(INSTR_TRY);

        size_t catch_offset = state.code.count;
        emit_int(0);

        size_t finally_offset = state.code.count;
        emit_int(-1);

        size_t end_offset = state.code.count;
        emit_int(-1);

        uint64_t try_save = state.try;
        state.try = ++t;

        emit_statement(s->try.s);

        PLACEHOLDER_JUMP(INSTR_JUMP, size_t end);

        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        PATCH_JUMP(catch_offset);

        for (int i = 0; i < s->try.patterns.count; ++i)
                emit_case(s->try.patterns.items[i], NULL, s->try.handlers.items[i]);

        emit_instr(INSTR_FINALLY);
        emit_instr(INSTR_THROW);

        patch_jumps_to(&state.match_successes, state.code.count);
        PATCH_JUMP(end);

        state.match_successes = successes_save;

        state.try = try_save;

        if (s->try.finally != NULL) {
                PATCH_JUMP(finally_offset);
                emit_statement(s->try.finally);
                PATCH_JUMP(end_offset);
                emit_instr(INSTR_NOP);
        }

        emit_instr(INSTR_POP_TRY);
}

static void
emit_while_loop(struct statement const *s)
{
        offset_vector cont_save = state.continues;
        offset_vector brk_save = state.breaks;
        bool each_loop_save = state.each_loop;
        state.each_loop = false;
        uint64_t loop_save = state.loop;
        state.loop = loop_save;
        vec_init(state.continues);
        vec_init(state.breaks);

        size_t begin = state.code.count;

        emit_checks(s->while_loop.check);
        emit_expression(s->while_loop.cond);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, size_t end);

        emit_statement(s->while_loop.body);

        JUMP(begin);

        PATCH_JUMP(end);

        patch_loop_jumps(begin, state.code.count);

        state.continues = cont_save;
        state.breaks = brk_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_for_loop(struct statement const *s)
{
        offset_vector cont_save = state.continues;
        offset_vector brk_save = state.breaks;
        bool each_loop_save = state.each_loop;
        state.each_loop = false;
        uint64_t loop_save = state.loop;
        state.loop = ++t;
        vec_init(state.continues);
        vec_init(state.breaks);

        if (s->for_loop.init != NULL)
                emit_statement(s->for_loop.init);

        PLACEHOLDER_JUMP(INSTR_JUMP, size_t skip_next);

        size_t begin = state.code.count;

        emit_checks(s->for_loop.check);
        if (s->for_loop.next != NULL) {
                emit_expression(s->for_loop.next);
                emit_instr(INSTR_POP);
        }

        PATCH_JUMP(skip_next);

        size_t end_jump;
        if (s->for_loop.cond != NULL) {
                emit_expression(s->for_loop.cond);
                PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, end_jump);
        }

        emit_statement(s->for_loop.body);

        JUMP(begin);

        if (s->for_loop.cond != NULL)
                PATCH_JUMP(end_jump);

        patch_loop_jumps(begin, state.code.count);

        state.continues = cont_save;
        state.breaks = brk_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_try_match(struct expression const *pattern)
{
        switch (pattern->type) {
        case EXPRESSION_IDENTIFIER:
                if (strcmp(pattern->identifier, "_") == 0) {
                        /* nothing to do */
                } else {
                        emit_instr(INSTR_TARGET_VAR);
                        emit_symbol(pattern->symbol->symbol);
                        emit_instr(INSTR_ASSIGN);
                }
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_instr(INSTR_TRY_ASSIGN_NON_NIL);
                emit_symbol(pattern->symbol->symbol);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                break;
        case EXPRESSION_MUST_EQUAL:
                emit_instr(INSTR_ENSURE_EQUALS_VAR);
                emit_symbol(pattern->symbol->symbol);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                break;
        case EXPRESSION_VIEW_PATTERN:
                emit_instr(INSTR_DUP);
                emit_expression(pattern->left);
                emit_instr(INSTR_CALL);
                emit_int(1);
                emit_try_match(pattern->right);
                emit_instr(INSTR_POP);
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < pattern->elements.count; ++i) {
                        if (pattern->elements.items[i]->type == EXPRESSION_MATCH_REST) {
                                emit_instr(INSTR_ARRAY_REST);
                                emit_symbol(pattern->elements.items[i]->symbol->symbol);
                                emit_int(i);
                                vec_push(state.match_fails, state.code.count);
                                emit_int(0);

                                if (i + 1 != pattern->elements.count)
                                        fail("the *<id> array-matching pattern must be the last pattern in the array");
                        } else {
                                emit_instr(INSTR_TRY_INDEX);
                                emit_int(i);
                                vec_push(state.match_fails, state.code.count);
                                emit_int(0);

                                emit_try_match(pattern->elements.items[i]);

                                emit_instr(INSTR_POP);
                        }
                }

                if (pattern->elements.count == 0 || pattern->elements.items[pattern->elements.count - 1]->type != EXPRESSION_MATCH_REST) {
                        emit_instr(INSTR_ENSURE_LEN);
                        emit_int(pattern->elements.count);
                        vec_push(state.match_fails, state.code.count);
                        emit_int(0);
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
                emit_instr(INSTR_TRY_REGEX);
                emit_symbol((uintptr_t) pattern->regex);
                emit_symbol((uintptr_t) pattern->extra);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
                break;
        default:
                emit_instr(INSTR_DUP);
                emit_expression(pattern);
                emit_instr(INSTR_EQ);
                emit_instr(INSTR_JUMP_IF_NOT);
                vec_push(state.match_fails, state.code.count);
                emit_int(0);
        }
}

static void
emit_case(struct expression const *pattern, struct expression const *condition, struct statement const *s)
{
        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);
        
        emit_instr(INSTR_SAVE_STACK_POS);
        emit_try_match(pattern);

        size_t failcond;
        if (condition != NULL) {
                emit_expression(condition);
                emit_instr(INSTR_JUMP_IF_NOT);
                failcond = state.code.count;
                emit_int(0);
        }

        emit_instr(INSTR_RESTORE_STACK_POS);

        if (s != NULL)
                emit_statement(s);

        emit_instr(INSTR_JUMP);
        vec_push(state.match_successes, state.code.count);
        emit_int(0);

        if (condition != NULL)
                PATCH_JUMP(failcond);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;
}

static void
emit_expression_case(struct expression const *pattern, struct expression const *condition, struct expression const *e)
{
        offset_vector fails_save = state.match_fails;
        vec_init(state.match_fails);
        
        emit_instr(INSTR_SAVE_STACK_POS);
        emit_try_match(pattern);

        size_t failcond;
        if (condition != NULL) {
                emit_expression(condition);
                emit_instr(INSTR_JUMP_IF_NOT);
                failcond = state.code.count;
                emit_int(0);
        }

        /*
         * Go back to where the subject of the match is on top of the stack,
         * then pop it and execute the code to produce the result of this branch.
         */
        emit_instr(INSTR_RESTORE_STACK_POS);
        emit_instr(INSTR_POP);
        emit_expression(e);

        /*
         * We've successfully matched a pattern+condition and produced a result, so we jump
         * to the end of the match expression. i.e., there is no fallthrough.
         */
        emit_instr(INSTR_JUMP);
        vec_push(state.match_successes, state.code.count);
        emit_int(0);

        if (condition != NULL)
                PATCH_JUMP(failcond);

        patch_jumps_to(&state.match_fails, state.code.count);
        emit_instr(INSTR_RESTORE_STACK_POS);

        state.match_fails = fails_save;
}

static void
emit_match_statement(struct statement const *s)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        emit_expression(s->match.e);

        for (int i = 0; i < s->match.patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                emit_case(s->match.patterns.items[i], s->match.conds.items[i], s->match.statements.items[i]);
        }

        /*
         * Nothing matched. This is a runtime errror.
         */
        emit_instr(INSTR_BAD_MATCH);

        patch_jumps_to(&state.match_successes, state.code.count);

        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
}

static void
emit_while_match(struct statement const *s)
{
        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        bool each_loop_save = state.each_loop;
        state.each_loop = false;
        uint64_t loop_save = state.loop;
        state.loop = loop_save;
        vec_init(state.breaks);
        vec_init(state.continues);
        vec_init(state.match_successes);

        size_t begin = state.code.count;

        emit_checks(s->match.check);

        emit_expression(s->match.e);

        for (int i = 0; i < s->match.patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                emit_case(s->match.patterns.items[i], s->match.conds.items[i], s->match.statements.items[i]);
        }

        /*
         * If nothing matches, we jump out of the loop.
         */
        PLACEHOLDER_JUMP(INSTR_JUMP, size_t finished);

        patch_jumps_to(&state.match_successes, state.code.count);

        /*
         * Something matched, so we iterate again.
         */
        JUMP(begin);

        PATCH_JUMP(finished);
        patch_loop_jumps(begin, state.code.count);

        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_while_let(struct statement const *s)
{
        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        bool each_loop_save = state.each_loop;
        state.each_loop = false;
        uint64_t loop_save = state.loop;
        state.loop = loop_save;
        vec_init(state.breaks);
        vec_init(state.continues);
        vec_init(state.match_successes);

        size_t begin = state.code.count;

        emit_checks(s->while_let.check);

        emit_expression(s->while_let.e);

        emit_case(s->while_let.pattern, NULL, s->while_let.block);

        /*
         * We failed to match, so we jump out.
         */
        PLACEHOLDER_JUMP(INSTR_JUMP, size_t finished);

        patch_jumps_to(&state.match_successes, state.code.count);

        /*
         * We matched, so we iterate again.
         */
        emit_instr(INSTR_POP);
        JUMP(begin);

        PATCH_JUMP(finished);
        patch_loop_jumps(begin, state.code.count);

        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
        state.breaks = brk_save;
        state.continues = cont_save;
        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_if_let(struct statement const *s)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        emit_expression(s->if_let.e);

        emit_case(s->if_let.pattern, NULL, s->if_let.then);

        if (s->if_let.otherwise != NULL)
                emit_statement(s->if_let.otherwise);

        patch_jumps_to(&state.match_successes, state.code.count);

        emit_instr(INSTR_POP);

        state.match_successes = successes_save;
}

static void
emit_match_expression(struct expression const *e)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        emit_expression(e->subject);

        for (int i = 0; i < e->patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                emit_expression_case(e->patterns.items[i], e->conds.items[i], e->thens.items[i]);
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
emit_each_loop(struct statement const *s)
{
        bool each_loop_save = state.each_loop;
        state.each_loop = true;

        uint64_t loop_save = state.loop;
        state.loop = ++t;

        emit_expression(s->each.array);

        emit_instr(INSTR_FOR_EACH);

        size_t start = state.code.count;
        emit_int(0);

        emit_checks(s->each.check);

        emit_assignment(s->each.target, NULL);
        emit_instr(INSTR_POP);
        emit_statement(s->each.body);
        emit_instr(INSTR_HALT);

        int n = state.code.count - start - sizeof (int);
        memcpy(state.code.items + start, &n, sizeof (int));

        state.each_loop = each_loop_save;
        state.loop = loop_save;
}

static void
emit_target(struct expression *target)
{
        switch (target->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
                if (target->local) {
                        emit_instr(INSTR_TARGET_VAR);
                } else {
                        emit_instr(INSTR_TARGET_REF);
                        addref(target->symbol->symbol);
                }
                emit_symbol(target->symbol->symbol);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                emit_expression(target->object);
                emit_instr(INSTR_TARGET_MEMBER);
                emit_string(target->member_name);
                break;
        case EXPRESSION_SUBSCRIPT:
                emit_expression(target->container);
                emit_expression(target->subscript);
                emit_instr(INSTR_TARGET_SUBSCRIPT);
                break;
        default:
                fail("oh no!");
        }
}

static void
emit_assignment(struct expression *target, struct expression const *e)
{

        struct symbol *tmp;
        struct expression container, index, subscript;

        if (e != NULL)
                emit_expression(e);

        switch (target->type) {
        case EXPRESSION_ARRAY:
                tmp = tmpsymbol();
                emit_instr(INSTR_PUSH_VAR);
                emit_symbol(tmp->symbol);
                emit_instr(INSTR_TARGET_VAR);
                emit_symbol(tmp->symbol);
                emit_instr(INSTR_ASSIGN);
                container = EXPR(.type = EXPRESSION_IDENTIFIER, .symbol = tmp, .local = true);
                index = EXPR(.type = EXPRESSION_INTEGER);
                subscript = EXPR(.type = EXPRESSION_SUBSCRIPT, .container = &container, .subscript = &index);
                for (int i = 0; i < target->elements.count; ++i) {
                        index.integer = i;
                        emit_assignment(target->elements.items[i], &subscript);
                        emit_instr(INSTR_POP);
                }
                emit_instr(INSTR_POP_VAR);
                emit_symbol(tmp->symbol);
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_instr(INSTR_UNTAG_OR_DIE);
                emit_int(target->symbol->tag);
                emit_assignment(target->tagged, NULL);
                break;
        case EXPRESSION_MATCH_NOT_NIL:
                emit_instr(INSTR_DIE_IF_NIL);
                emit_target(target);
                emit_instr(INSTR_ASSIGN);
                break;
        default:
                emit_target(target);
                emit_instr(INSTR_ASSIGN);
        }
}

static void
emit_expression(struct expression const *e)
{
        state.loc = e->loc;
        add_location(e->loc);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (e->local) {
                        emit_instr(INSTR_LOAD_VAR);
                } else {
                        emit_instr(INSTR_LOAD_REF);
                        addref(e->symbol->symbol);
                }
                emit_symbol(e->symbol->symbol);
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
        case EXPRESSION_EQ:
                emit_assignment(e->target, e->value);
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
                emit_symbol((uintptr_t) e->extra);
                emit_symbol((uintptr_t) e->pattern);
                break;
        case EXPRESSION_ARRAY:
                for (int i = e->elements.count - 1; i >= 0; --i)
                        emit_expression(e->elements.items[i]);
                emit_instr(INSTR_ARRAY);
                emit_int(e->elements.count);
                break;
        case EXPRESSION_DICT:
                for (int i = e->keys.count - 1; i >= 0; --i) {
                        emit_expression(e->keys.items[i]);
                        if (e->values.items[i] == NULL)
                                emit_instr(INSTR_NIL);
                        else
                                emit_expression(e->values.items[i]);
                }
                emit_instr(INSTR_DICT);
                emit_int(e->keys.count);
                break;
        case EXPRESSION_NIL:
                emit_instr(INSTR_NIL);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                emit_expression(e->object);
                emit_instr(INSTR_MEMBER_ACCESS);
                emit_string(e->member_name);
                break;
        case EXPRESSION_SUBSCRIPT:
                emit_expression(e->container);
                emit_expression(e->subscript);
                emit_instr(INSTR_SUBSCRIPT);
                break;
        case EXPRESSION_FUNCTION_CALL:
                for (size_t i = 0; i < e->args.count; ++i)
                        emit_expression(e->args.items[i]);
                emit_expression(e->function);
                emit_instr(INSTR_CALL);
                emit_int(e->args.count);
                break;
        case EXPRESSION_METHOD_CALL:
                for (size_t i = 0; i < e->method_args.count; ++i)
                        emit_expression(e->method_args.items[i]);
                emit_expression(e->object);
                emit_instr(INSTR_CALL_METHOD);
                emit_string(e->method_name);
                emit_int(e->method_args.count);
                break;
        case EXPRESSION_FUNCTION:
                emit_instr(INSTR_FUNCTION);
                emit_function(e);
                break;
        case EXPRESSION_CONDITIONAL:
                emit_conditional_expression(e);
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
        case EXPRESSION_PREFIX_BANG:
                emit_expression(e->operand);
                emit_instr(INSTR_NOT);
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
                emit_target(e->operand);
                emit_instr(INSTR_PRE_INC);
                break;
        case EXPRESSION_PREFIX_DEC:
                emit_target(e->operand);
                emit_instr(INSTR_PRE_DEC);
                break;
        case EXPRESSION_POSTFIX_INC:
                emit_target(e->operand);
                emit_instr(INSTR_POST_INC);
                break;
        case EXPRESSION_POSTFIX_DEC:
                emit_target(e->operand);
                emit_instr(INSTR_POST_DEC);
                break;
        case EXPRESSION_PLUS_EQ:
                emit_target(e->target);
                emit_expression(e->value);
                emit_instr(INSTR_MUT_ADD);
                break;
        case EXPRESSION_STAR_EQ:
                emit_target(e->target);
                emit_expression(e->value);
                emit_instr(INSTR_MUT_MUL);
                break;
        case EXPRESSION_DIV_EQ:
                emit_target(e->target);
                emit_expression(e->value);
                emit_instr(INSTR_MUT_DIV);
                break;
        case EXPRESSION_MINUS_EQ:
                emit_target(e->target);
                emit_expression(e->value);
                emit_instr(INSTR_MUT_SUB);
                break;
        case EXPRESSION_LIST:
                fail("list in invalid context");
                break;
        }
}

static void
emit_statement(struct statement const *s)
{
        state.loc = s->loc;

        switch (s->type) {
        case STATEMENT_BLOCK:
                for (int i = 0; i < s->statements.count; ++i)
                        emit_statement(s->statements.items[i]);
                break;
        case STATEMENT_MATCH:
                emit_match_statement(s);
                break;
        case STATEMENT_CONDITIONAL:
                emit_conditional_statement(s);
                break;
        case STATEMENT_FOR_LOOP:
                emit_for_loop(s);
                break;
        case STATEMENT_EACH_LOOP:
                emit_each_loop(s);
                break;
        case STATEMENT_WHILE_LOOP:
                emit_while_loop(s);
                break;
        case STATEMENT_WHILE_MATCH:
                emit_while_match(s);
                break;
        case STATEMENT_WHILE_LET:
                emit_while_let(s);
                break;
        case STATEMENT_IF_LET:
                emit_if_let(s);
                break;
        case STATEMENT_EXPRESSION:
                emit_expression(s->expression);
                emit_instr(INSTR_POP);
                break;
        case STATEMENT_DEFINITION:
                emit_assignment(s->target, s->value);
                emit_instr(INSTR_POP);
                break;
        case STATEMENT_TAG_DEFINITION:
                for (int i = 0; i < s->tag.methods.count; ++i) {
                        emit_instr(INSTR_FUNCTION);
                        emit_function(s->tag.methods.items[i]);
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
                        emit_instr(INSTR_FUNCTION);
                        emit_function(s->class.methods.items[i]);
                }

                emit_instr(INSTR_DEFINE_CLASS);
                emit_int(s->class.symbol);
                emit_int(s->class.super == NULL ? -1 : s->class.super->symbol->class);
                emit_int(s->class.methods.count);

                for (int i = s->class.methods.count; i > 0; --i)
                        emit_string(s->class.methods.items[i - 1]->name);

                break;
        case STATEMENT_TRY:
                emit_try(s);
                break;
        case STATEMENT_THROW:
                emit_throw(s);
                break;
        case STATEMENT_RETURN:
                if (state.function_depth == 0)
                        fail("invalid 'return' statement (not inside of a function)");
                if (s->return_value != NULL)
                        emit_expression(s->return_value);
                else
                        emit_instr(INSTR_NIL);
                /* returning from within a for-each loop must be handled specially */
                if (state.each_loop) {
                        emit_instr(INSTR_HALT);
                        break;
                }
                for (int i = 0; i < state.bound_symbols.count; ++i) {
                        emit_instr(INSTR_POP_VAR);
                        emit_symbol(state.bound_symbols.items[i]->symbol);
                }
                if (state.try)
                        emit_instr(INSTR_FINALLY);
                emit_instr(INSTR_RETURN);
                break;
        case STATEMENT_BREAK:
                if (state.try > state.loop)
                        emit_instr(INSTR_FINALLY);
                if (state.each_loop) {
                        emit_instr(INSTR_BREAK_EACH);
                } else {
                        emit_instr(INSTR_JUMP);
                        vec_push(state.breaks, state.code.count);
                        emit_int(0);
                }
                break;
        case STATEMENT_CONTINUE: 
                if (state.try > state.loop)
                        emit_instr(INSTR_FINALLY);
                if (state.each_loop) {
                        emit_instr(INSTR_HALT);
                } else {
                        emit_instr(INSTR_JUMP); 
                        vec_push(state.continues, state.code.count);
                        emit_int(0);
                }
                break;
        }
}

static void
emit_new_globals(void)
{
        for (int i = global_count; i < global->function_symbols.count; ++i) {
                struct symbol *s = global->function_symbols.items[i];
                if (s->symbol >= builtin_count) {
                        emit_instr(INSTR_PUSH_VAR);
                        emit_symbol(s->symbol);
                        if (s->tag != -1) {
                                emit_instr(INSTR_TAG);
                                emit_int(s->tag);
                                emit_instr(INSTR_TARGET_VAR);
                                emit_symbol(s->symbol);
                                emit_instr(INSTR_ASSIGN);
                                emit_instr(INSTR_POP);
                        } else if (s->class != -1) {
                                emit_instr(INSTR_CLASS);
                                emit_int(s->class);
                                emit_instr(INSTR_TARGET_VAR);
                                emit_symbol(s->symbol);
                                emit_instr(INSTR_ASSIGN);
                                emit_instr(INSTR_POP);
                        }
                }
        }

        global_count = global->function_symbols.count;
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
compile(char const *source)
{
        struct statement **p = parse(source, state.filename);
        if (p == NULL) {
                err_msg = parse_error();
                longjmp(jb, 1);
        }

        for (size_t i = 0; p[i] != NULL; ++i)
                symbolize_statement(state.global, p[i]);

        for (int i = 0; i < state.exports.count; ++i) {
                struct symbol *s = scope_lookup(state.global, state.exports.items[i]);
                if (s == NULL)
                        fail("attempt to export non-existent variable '%s'", state.exports.items[i]);
                s->public = true;
        }

        emit_new_globals();

        for (size_t i = 0; p[i] != NULL; ++i)
                emit_statement(p[i]);

        emit_instr(INSTR_HALT);

        /*
         * Add all of the location information from this compliation unit to the global list.
         */
        add_location((struct location){});
        patch_location_info();
        vec_push(location_lists, state.expression_locations);
}

static void
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
                goto import;

        char pathbuf[512];
        char const *home = getenv("HOME");
        if (home == NULL)
                fail("unable to get $HOME from the environment");

        snprintf(pathbuf, sizeof pathbuf, "%s/.ty/%s.ty", home, name);

        char *source = slurp(pathbuf);
        if (source == NULL)
                fail("failed to read file: %s", pathbuf);

        /*
         * Save the current compiler state so we can restore it after compiling
         * this module.
         */
        struct state save = state;
        state = freshstate();
        state.filename = pathbuf;

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

        emit_instr(INSTR_EXEC_CODE);
        emit_symbol((uintptr_t) m.code);

import:
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
        return err_msg;
}

void
compiler_init(void)
{
        tags_init();
        class_new("Object");
        state = freshstate();
        global = state.global;
}

char *
compiler_load_prelude(void)
{
        compile(slurp_module("prelude"));
        state.global = scope_new(state.global, false);
        return state.code.items;
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

        addsymbol(s, name)->public = true;

        builtin_count += 1;
}

char *
compiler_compile_source(char const *source, char const *filename)
{
        vec_init(state.code);
        vec_init(state.refs);
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

struct location
compiler_get_location(char const *code, char const **file)
{
        location_vector *locs = NULL;
        *file = NULL;

        uintptr_t c = (uintptr_t) code;

        /*
         * First do a linear search for the group of locations which
         * contains this one.
         */
        for (int i = 0; i < location_lists.count; ++i) {
                if (location_lists.items[i].count == 0)
                        continue;
                if (c < location_lists.items[i].items[0].p)
                        continue;
                if (c > vec_last(location_lists.items[i])->p)
                        continue;
                locs = &location_lists.items[i];
                break;
        }

        if (locs == NULL)
                return (struct location) { -1, -1 };

        /*
         * Now do a binary search within this group of locations.
         */
        int lo = 0,
            hi = locs->count - 1;

        while (lo <= hi) {
                int m = (lo / 2) + (hi / 2) + (lo & hi & 1);
                if      (c < locs->items[m].p) hi = m - 1;
                else if (c > locs->items[m].p) lo = m + 1;
                else                           break;
        }

        while (lo > 0 && (lo >= locs->count || locs->items[lo].p >= c))
                --lo;

        *file = locs->items[lo].filename;

        return locs->items[lo].loc;
}
