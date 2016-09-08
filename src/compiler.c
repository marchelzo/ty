#include <stdlib.h>
#include <stdio.h>
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
#include "object.h"
#include "functions.h"
#include "test.h"
#include "lex.h"
#include "parse.h"
#include "tags.h"
#include "vm.h"

#define emit_instr(i) LOG("emitting instr: %s", #i); _emit_instr(i)

#define PLACEHOLDER_JUMP(t, name) \
        emit_instr(t); \
        size_t name = state.code.count; \
        emit_int(0);

#define PATCH_JUMP(name) \
        jumpdistance = state.code.count - name - sizeof (int); \
        memcpy(state.code.items + name, &jumpdistance, sizeof jumpdistance); \

#define JUMP(loc) \
        emit_instr(INSTR_JUMP); \
        emit_int(loc - state.code.count - sizeof (int));

/*
 * Flags for properties of lvalues.
 *
 * LV_PUB  - only applies to top-level declarations, and it means the identifiers will be exported (visible to other modules).
 * LV_DECL - means that the lvalue is for a declaration and not an ordinary assignment.
 * LV_NONE - just an alias for none of the above being true.
 */
enum {
        LV_NONE = 0,
        LV_DECL = 1,
        LV_PUB  = 2,
};

/* expression location */
struct eloc {
        union {
                uintptr_t p;
                size_t offset;
        };
        struct expression const *e;
};

struct scope {
        bool function;
        bool external;
        vec(int) func_symbols;
        vec(int) symbols;
        vec(char const *) identifiers;
        struct scope *parent;
        struct scope *func;
};

struct module {
        char const *path;
        char *code;
        struct scope *scope;
};

struct import {
        char *name;
        struct scope *scope;
};

typedef vec(struct import)    import_vector;
typedef vec(struct reference) reference_vector;
typedef vec(struct eloc)      location_vector;
typedef vec(int)              symbol_vector;
typedef vec(size_t)           offset_vector;
typedef vec(char)             byte_vector;

/*
 * State which is local to a single compilation unit.
 */
struct state {
        byte_vector code;

        symbol_vector bound_symbols;
        reference_vector refs;
        
        offset_vector breaks;
        offset_vector continues;
        offset_vector match_fails;
        offset_vector match_successes;

        int function_depth;

        import_vector imports;

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

static int symbol;
static int jumpdistance;
static vec(struct module) modules;
static struct state state;

static vec(location_vector) location_lists;
static symbol_vector public_symbols;

static struct scope *global;
static int global_count;

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
emit_assignment(struct expression *target, struct expression const *e, int i);

static void
import_module(char *name, char *as);

static char const *tags[] = {
        "None",
        "Some",
        "Ok",
        "Err",
};
static size_t tagcount = sizeof tags / sizeof tags[0];

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

        LOG("Failing with error: %s", err_buf);

        va_end(ap);

        longjmp(jb, 1);
}

static void
add_location(struct expression const *e)
{
        if (e != NULL)
                ((struct expression *)e)->filename = state.filename;

        vec_push(
                state.expression_locations,
                ((struct eloc){
                        .offset = state.code.count,
                        .e = e
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

/*
 * Is 'symbol' publicly visible?
 */
static bool
ispublic(int symbol)
{
        int lo = 0,
            hi = public_symbols.count - 1;

        while (lo <= hi) {
                int m = (lo / 2) + (hi / 2) + (lo & hi & 1);
                if (public_symbols.items[m] < symbol) {
                        lo = m + 1;
                } else if (public_symbols.items[m] > symbol) {
                        hi = m - 1;
                } else {
                        return true;
                }
        }

        return false;
}

inline static bool
locallydefined(struct scope const *scope, char const *name)
{
        /*
         * _ is allowed to be "re-declared".
         */
        if (strcmp(name, "_") == 0) {
                return false;
        }

        for (int i = 0; i < scope->identifiers.count; ++i) {
                if (strcmp(scope->identifiers.items[i], name) == 0) {
                        return true;
                }
        }

        return false;
}

inline static void
definetag(char const *tag)
{
        int t = tags_new(tag);

        if (locallydefined(global, tag)) {
                fail("%s is a built-in tag and cannot be re-declared", tag);
        }

        if (locallydefined(state.global, tag)) {
                fail("redeclaration of tag: %s", tag);
        }

        vec_push(state.global->identifiers, tag);
        vec_push(state.global->symbols, t);
}

inline static int
addsymbol(struct scope *scope, char const *name, bool pub)
{
        assert(name != NULL);

        if (locallydefined(scope, name)) {
                fail("redeclaration of variable: %s", name);
        }

        vec_push(scope->identifiers, name);
        vec_push(scope->symbols, symbol);

        if (scope->func != NULL) {
                vec_push(scope->func->func_symbols, symbol);
        }

        if (pub) {
                vec_push(public_symbols, symbol);
        }

        LOG("adding symbol: %s -> %d", name, symbol);
        return symbol++;
}

inline static int
getsymbol(struct scope const *scope, char const *name, bool *local)
{
        if (local != NULL) {
                *local = true;
        }

        /*
         * _ can never be used as anything but an lvalue.
         */
        if (strcmp(name, "_") == 0) {
                fail("the special identifier '_' can only be used as an lvalue");
        }

        while (scope != NULL) {
                for (int i = 0; i < scope->identifiers.count; ++i) {
                        if (strcmp(scope->identifiers.items[i], name) == 0) {
                                if (scope->external && !ispublic(scope->symbols.items[i])) {
                                        fail("reference to non-public external variable: %s", name);
                                }
                                return scope->symbols.items[i];
                        }
                }

                if (scope->function && local != NULL) {
                        *local = false;
                }

                scope = scope->parent;
        }

        fail("reference to undefined variable: %s", name);
}

inline static int
tmpsymbol(int i)
{
        static char idbuf[8];
        assert(i <= 9999999 && i >= 0);

        sprintf(idbuf, "%d", i);

        if (locallydefined(global, idbuf)) {
                return getsymbol(global, idbuf, NULL);
        } else {
                return addsymbol(global, sclone(idbuf), false);
        }
}

static struct scope *
newscope(struct scope *parent, bool function)
{
        struct scope *s = alloc(sizeof *s);

        s->function = function;
        s->parent = parent;
        s->func = (function || parent == NULL) ? s : parent->func;
        s->external = false;

        vec_init(s->symbols);
        vec_init(s->identifiers);
        vec_init(s->func_symbols);

        return s;
}

static struct state
freshstate(void)
{
        struct state s;

        vec_init(s.code);

        vec_init(s.refs);
        vec_init(s.bound_symbols);

        vec_init(s.breaks);
        vec_init(s.continues);

        vec_init(s.imports);

        s.global = newscope(global, false);

        s.function_depth = 0;

        s.filename = NULL;
        s.loc = (struct location){ 0, 0 };

        vec_init(s.expression_locations);

        return s;
}

static struct scope *
get_import_scope(char const *name)
{
        LOG("LOOKING FOR MODULE: %s", name);

        for (int i = 0; i < state.imports.count; ++i) {
                if (strcmp(name, state.imports.items[i].name) == 0) {
                        LOG("Returning: %s == %s", name, state.imports.items[i].name);
                        return state.imports.items[i].scope;
                }
        }

        fail("reference to undefined module: %s", name);
}

static void
symbolize_lvalue(struct scope *scope, struct expression *target, int flags)
{
        state.loc = target->loc;

        switch (target->type) {
        case EXPRESSION_IDENTIFIER:
                if (flags & LV_DECL) {
                        target->symbol = addsymbol(scope, target->identifier, flags & LV_PUB);
                        target->local = true;
                } else {
                        target->symbol = getsymbol(scope, target->identifier, &target->local);
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                symbolize_lvalue(scope, target->tagged, flags);
                target->tag = getsymbol(
                        ((target->module == NULL) ? state.global : get_import_scope(target->module)),
                        target->identifier,
                        NULL
                );
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < target->elements.count; ++i) {
                        symbolize_lvalue(scope, target->elements.items[i], flags);
                }
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
        if (e == NULL) {
                return;
        }

        state.loc = e->loc;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                e->symbol = addsymbol(scope, e->identifier, true);
                break;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < e->elements.count; ++i) {
                        symbolize_pattern(scope, e->elements.items[i]);
                }
                break;
        case EXPRESSION_VIEW_PATTERN:
                symbolize_expression(scope, e->left);
                symbolize_pattern(scope, e->right);
                break;
        case EXPRESSION_MATCH_REST:
                e->symbol = addsymbol(scope, e->identifier, true);
                break;
        case EXPRESSION_TAG_APPLICATION:
                e->tag = getsymbol(
                        ((e->module == NULL) ? state.global : get_import_scope(e->module)),
                        e->identifier,
                        NULL
                );
                symbolize_pattern(scope, e->tagged);
                break;
        default:
                symbolize_expression(scope, e);
        }
}

static void
symbolize_expression(struct scope *scope, struct expression *e)
{
        if (e == NULL) {
                return;
        }

        state.loc = e->loc;

        struct scope *subscope;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                LOG("symbolizing var: %s%s%s", e->identifier, (e->module == NULL ? "" : e->module), (e->module == NULL ? "" : "::"));
                e->symbol = getsymbol(
                        ((e->module == NULL) ? scope : get_import_scope(e->module)),
                        e->identifier,
                        &e->local
                );
                LOG("var %s local", e->local ? "is" : "is NOT");
                break;
        case EXPRESSION_SPECIAL_STRING:
                for (int i = 0; i < e->expressions.count; ++i) {
                        symbolize_expression(scope, e->expressions.items[i]);
                }
                break;
        case EXPRESSION_RANGE:
                symbolize_expression(scope, e->low);
                symbolize_expression(scope, e->high);
                break;
        case EXPRESSION_TAG:
                e->tag = getsymbol(
                        ((e->module == NULL) ? state.global : get_import_scope(e->module)),
                        e->identifier,
                        NULL
                );
                break;
        case EXPRESSION_TAG_APPLICATION:
                e->tag = getsymbol(
                        ((e->module == NULL) ? state.global : get_import_scope(e->module)),
                        e->identifier,
                        NULL
                );
                symbolize_expression(scope, e->tagged);
                break;
        case EXPRESSION_MATCH:
                symbolize_expression(scope, e->subject);
                for (int i = 0; i < e->patterns.count; ++i) {
                        subscope = newscope(scope, false);
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
                for (size_t i = 0;  i < e->args.count; ++i) {
                        symbolize_expression(scope, e->args.items[i]);
                }
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
                for (size_t i = 0;  i < e->method_args.count; ++i) {
                        symbolize_expression(scope, e->method_args.items[i]);
                }
                break;
        case EXPRESSION_EQ:
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MINUS_EQ:
                symbolize_expression(scope, e->value);
                symbolize_lvalue(scope, e->target, LV_NONE);
                break;
        case EXPRESSION_FUNCTION:

                if (e->name != NULL) {
                        scope = newscope(scope, false);
                        e->function_symbol = addsymbol(scope, e->name, false);
                } else {
                        e->function_symbol = -1;
                }

                scope = newscope(scope, true);

                vec_init(e->param_symbols);
                for (size_t i = 0; i < e->params.count; ++i) {
                        vec_push(e->param_symbols, addsymbol(scope, e->params.items[i], false));
                }
                symbolize_statement(scope, e->body);

                e->bound_symbols.items = scope->func_symbols.items;
                e->bound_symbols.count = scope->func_symbols.count;

                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i) {
                        symbolize_expression(scope, e->elements.items[i]);
                }
                break;
        case EXPRESSION_OBJECT:
                for (size_t i = 0; i < e->keys.count; ++i) {
                        symbolize_expression(scope, e->keys.items[i]);
                        symbolize_expression(scope, e->values.items[i]);
                }
                break;
        }
}

static void
symbolize_statement(struct scope *scope, struct statement *s)
{
        if (s == NULL) {
                return;
        }

        state.loc = s->loc;

        struct scope *subscope;

        switch (s->type) {
        case STATEMENT_IMPORT:
                import_module(s->import.module, s->import.as);
                break;
        case STATEMENT_EXPRESSION:
                symbolize_expression(scope, s->expression);
                break;
        case STATEMENT_TAG_DEFINITION:
                definetag(s->tag);
                break;
        case STATEMENT_BLOCK:
                scope = newscope(scope, false);
                for (size_t i = 0; i < s->statements.count; ++i) {
                        symbolize_statement(scope, s->statements.items[i]);
                }
                break;
        case STATEMENT_MATCH:
        case STATEMENT_WHILE_MATCH:
                symbolize_expression(scope, s->match.e);
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        subscope = newscope(scope, false);
                        symbolize_pattern(subscope, s->match.patterns.items[i]);
                        symbolize_expression(subscope, s->match.conds.items[i]);
                        symbolize_statement(subscope, s->match.statements.items[i]);
                }
                break;
        case STATEMENT_WHILE_LET:
                symbolize_expression(scope, s->while_let.e);
                subscope = newscope(scope, false);
                symbolize_pattern(subscope, s->while_let.pattern);
                symbolize_statement(subscope, s->while_let.block);
                break;
        case STATEMENT_IF_LET:
                symbolize_expression(scope, s->if_let.e);
                subscope = newscope(scope, false);
                symbolize_pattern(subscope, s->if_let.pattern);
                symbolize_statement(subscope, s->if_let.then);
                symbolize_statement(scope, s->if_let.otherwise); // note that this is not done in the subscope
                break;
        case STATEMENT_FOR_LOOP:
                scope = newscope(scope, false);
                symbolize_statement(scope, s->for_loop.init);
                symbolize_expression(scope, s->for_loop.cond);
                symbolize_expression(scope, s->for_loop.next);
                symbolize_statement(scope, s->for_loop.body);
                break;
        case STATEMENT_EACH_LOOP:
                scope = newscope(scope, false);
                symbolize_lvalue(scope, s->each.target, LV_DECL);
                symbolize_expression(scope, s->each.array);
                symbolize_statement(scope, s->each.body);
                break;
        case STATEMENT_WHILE_LOOP:
                symbolize_expression(scope, s->while_loop.cond);
                symbolize_statement(scope, s->while_loop.body);
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
                symbolize_lvalue(scope, s->target, (LV_DECL | (LV_PUB * s->pub)));
                break;
        }
}

static void
patch_jumps_to(offset_vector const *js, size_t location)
{
        for (int i = 0; i < js->count; ++i) {
                int distance = location - js->items[i] - sizeof (int);
                memcpy(state.code.items + js->items[i], &distance, sizeof distance);
        }
}

static void
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
        for (int i = 0; i < sizeof (int); ++i) {
                vec_push(state.code, s[i]);
        }
}

inline static void
emit_symbol(uintptr_t sym)
{
        LOG("emitting symbol: %"PRIuPTR, sym);
        char const *s = (char *) &sym;
        for (int i = 0; i < sizeof (uintptr_t); ++i) {
                vec_push(state.code, s[i]);
        }
}

inline static void
emit_integer(intmax_t k)
{
        
        LOG("emitting integer: %"PRIiMAX, k);
        char const *s = (char *) &k;
        for (int i = 0; i < sizeof (intmax_t); ++i) {
                vec_push(state.code, s[i]);
        }
}

inline static void
emit_boolean(bool b)
{
        
        LOG("emitting boolean: %s", b ? "true" : "false");
        char const *s = (char *) &b;
        for (int i = 0; i < sizeof (bool); ++i) {
                vec_push(state.code, s[i]);
        }
}

inline static void
emit_float(float f)
{
        
        LOG("emitting float: %f", f);
        char const *s = (char *) &f;
        for (int i = 0; i < sizeof (float); ++i) {
                vec_push(state.code, s[i]);
        }
}

inline static void
emit_string(char const *s)
{
        
        LOG("emitting string: %s", s);
        size_t n = strlen(s) + 1;
        for (int i = 0; i < n; ++i) {
                vec_push(state.code, s[i]);
        }
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


        emit_int(e->bound_symbols.count);
        for (int i = 0; i < e->bound_symbols.count; ++i) {
                LOG("bound sym: %d", e->bound_symbols.items[i]);
                emit_symbol(e->bound_symbols.items[i]);
        }

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

        emit_int(e->param_symbols.count);
        for (int i = 0; i < e->param_symbols.count; ++i) {
                emit_symbol(e->param_symbols.items[i]);
        }

        emit_int(state.refs.count);
        for (int i = 0; i < state.refs.count; ++i) {
                emit_symbol(state.refs.items[i].symbol);
                emit_symbol(state.refs.items[i].offset - start_offset);
        }

        state.refs = refs_save;
        state.bound_symbols = syms_save;
        --state.function_depth;

        if (e->function_symbol != -1) {
                emit_instr(INSTR_TARGET_VAR);
                emit_symbol(e->function_symbol);
                emit_instr(INSTR_ASSIGN);
        }
}

static void
emit_conditional_statement(struct statement const *s)
{
        emit_expression(s->conditional.cond);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF, then_branch);

        if (s->conditional.else_branch != NULL) {
                emit_statement(s->conditional.else_branch);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, end);

        PATCH_JUMP(then_branch);

        emit_statement(s->conditional.then_branch);

        PATCH_JUMP(end);
}

static void
emit_conditional_expression(struct expression const *e)
{
        emit_expression(e->cond);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, false_branch);

        emit_expression(e->then);

        PLACEHOLDER_JUMP(INSTR_JUMP, end);

        PATCH_JUMP(false_branch);

        emit_expression(e->otherwise);

        PATCH_JUMP(end);
}

static void
emit_and(struct expression const *left, struct expression const *right)
{
        emit_expression(left);
        emit_instr(INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, left_false);

        emit_instr(INSTR_POP);
        emit_expression(right);

        PATCH_JUMP(left_false);
}

static void
emit_or(struct expression const *left, struct expression const *right)
{
        emit_expression(left);
        emit_instr(INSTR_DUP);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF, left_true);

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
emit_while_loop(struct statement const *s)
{
        offset_vector cont_save = state.continues;
        offset_vector brk_save = state.breaks;
        vec_init(state.continues);
        vec_init(state.breaks);

        size_t begin = state.code.count;

        emit_expression(s->while_loop.cond);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, end);

        emit_statement(s->while_loop.body);

        JUMP(begin);

        PATCH_JUMP(end);

        patch_loop_jumps(begin, state.code.count);

        state.continues = cont_save;
        state.breaks = brk_save;
}

static void
emit_for_loop(struct statement const *s)
{
        offset_vector cont_save = state.continues;
        offset_vector brk_save = state.breaks;
        vec_init(state.continues);
        vec_init(state.breaks);

        if (s->for_loop.init != NULL) {
                emit_statement(s->for_loop.init);
        }

        PLACEHOLDER_JUMP(INSTR_JUMP, skip_next);

        size_t begin = state.code.count;

        emit_expression(s->for_loop.next);
        emit_instr(INSTR_POP);

        PATCH_JUMP(skip_next);

        emit_expression(s->for_loop.cond);
        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, end_jump);

        emit_statement(s->for_loop.body);

        JUMP(begin);

        PATCH_JUMP(end_jump);

        patch_loop_jumps(begin, state.code.count);

        state.continues = cont_save;
        state.breaks = brk_save;
}

static void
emit_try_match(struct expression const *pattern)
{
        switch (pattern->type) {
        case EXPRESSION_IDENTIFIER:
                /*
                 * The special identifier '_' matches anything, even nil. Ordinary identifiers will _not_
                 * match nil.
                 */
                if (strcmp(pattern->identifier, "_") == 0) {
                        /* nothing to do */
                } else {
                        emit_instr(INSTR_TRY_ASSIGN_NON_NIL);
                        emit_symbol(pattern->symbol);
                        vec_push(state.match_fails, state.code.count);
                        emit_int(0);
                }
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
                                emit_symbol(pattern->elements.items[i]->symbol);
                                emit_int(i);
                                vec_push(state.match_fails, state.code.count);
                                emit_int(0);

                                if (i + 1 != pattern->elements.count) {
                                        fail("the *<id> array-matching pattern must be the last pattern in the array");
                                }
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
                emit_int(pattern->tag);
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

        emit_statement(s);

        emit_instr(INSTR_JUMP);
        vec_push(state.match_successes, state.code.count);
        emit_int(0);

        if (condition != NULL) {
                PATCH_JUMP(failcond);
        }

        emit_instr(INSTR_RESTORE_STACK_POS);
        patch_jumps_to(&state.match_fails, state.code.count);

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

        if (condition != NULL) {
                PATCH_JUMP(failcond);
        }

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
        vec_init(state.breaks);
        vec_init(state.continues);
        vec_init(state.match_successes);

        size_t begin = state.code.count;

        emit_expression(s->match.e);

        for (int i = 0; i < s->match.patterns.count; ++i) {
                LOG("emitting case %d", i + 1);
                emit_case(s->match.patterns.items[i], s->match.conds.items[i], s->match.statements.items[i]);
        }

        /*
         * If nothing matches, we jump out of the loop.
         */
        PLACEHOLDER_JUMP(INSTR_JUMP, finished);

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
}

static void
emit_while_let(struct statement const *s)
{
        offset_vector brk_save = state.breaks;
        offset_vector cont_save = state.continues;
        offset_vector successes_save = state.match_successes;
        vec_init(state.breaks);
        vec_init(state.continues);
        vec_init(state.match_successes);

        size_t begin = state.code.count;

        emit_expression(s->while_let.e);

        emit_case(s->while_let.pattern, NULL, s->while_let.block);

        /*
         * We failed to match, so we jump out.
         */
        PLACEHOLDER_JUMP(INSTR_JUMP, finished);

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
}

static void
emit_if_let(struct statement const *s)
{
        offset_vector successes_save = state.match_successes;
        vec_init(state.match_successes);

        emit_expression(s->if_let.e);

        emit_case(s->if_let.pattern, NULL, s->if_let.then);

        if (s->if_let.otherwise != NULL) {
                emit_statement(s->if_let.otherwise);
        }

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
        offset_vector cont_save = state.continues;
        offset_vector brk_save = state.breaks;
        vec_init(state.continues);
        vec_init(state.breaks);

        emit_expression(s->each.array);

        int array_sym = tmpsymbol(0);
        emit_instr(INSTR_PUSH_VAR);
        emit_symbol(array_sym);

        int counter_sym = tmpsymbol(1);
        emit_instr(INSTR_PUSH_VAR);
        emit_symbol(counter_sym);

        emit_instr(INSTR_TARGET_VAR);
        emit_symbol(array_sym);
        emit_instr(INSTR_ASSIGN);
        emit_instr(INSTR_POP);

        emit_instr(INSTR_INTEGER);
        emit_integer(-1);

        assert(array_sym != counter_sym);

        emit_instr(INSTR_TARGET_VAR);
        emit_symbol(counter_sym);
        emit_instr(INSTR_ASSIGN);
        emit_instr(INSTR_POP);

        size_t begin = state.code.count;

        emit_instr(INSTR_INC);
        emit_symbol(counter_sym);

        emit_instr(INSTR_LOAD_VAR);
        emit_symbol(counter_sym);
        emit_instr(INSTR_LOAD_VAR);
        emit_symbol(array_sym);
        emit_instr(INSTR_LEN);
        emit_instr(INSTR_LT);

        PLACEHOLDER_JUMP(INSTR_JUMP_IF_NOT, end);

        struct expression array = { .type = EXPRESSION_IDENTIFIER, .symbol = array_sym, .local = true };
        struct expression index = { .type = EXPRESSION_IDENTIFIER, .symbol = counter_sym, .local = true };
        struct expression subscript = { .type = EXPRESSION_SUBSCRIPT, .container = &array, .subscript = &index };
        emit_assignment(s->each.target, &subscript, 2);
        emit_instr(INSTR_POP);
        emit_statement(s->each.body);

        JUMP(begin);

        PATCH_JUMP(end);

        patch_loop_jumps(begin, state.code.count);

        state.continues = cont_save;
        state.breaks = brk_save;
}

static void
emit_target(struct expression *target)
{
        switch (target->type) {
        case EXPRESSION_IDENTIFIER:
                if (target->local) {
                        emit_instr(INSTR_TARGET_VAR);
                } else {
                        emit_instr(INSTR_TARGET_REF);
                        addref(target->symbol);
                }
                emit_symbol(target->symbol);
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
emit_assignment(struct expression *target, struct expression const *e, int i)
{
        int tmp;
        struct expression container, subscript;

        switch (target->type) {
        case EXPRESSION_ARRAY:
                tmp = tmpsymbol(i);
                emit_expression(e);
                emit_instr(INSTR_PUSH_VAR);
                emit_symbol(tmp);
                emit_instr(INSTR_TARGET_VAR);
                emit_symbol(tmp);
                emit_instr(INSTR_ASSIGN);
                container = (struct expression){ .type = EXPRESSION_IDENTIFIER, .symbol = tmp, .local = true, .loc = {42, 42} };
                for (int j = 0; j < target->elements.count; ++j) {
                        subscript = (struct expression){ .type = EXPRESSION_INTEGER, .integer = j, .loc = {42, 42} };
                        emit_assignment(target->elements.items[j], &(struct expression){ .type = EXPRESSION_SUBSCRIPT, .container = &container, .subscript = &subscript, .loc = {42, 42}}, i + 1);
                        emit_instr(INSTR_POP);
                }
                emit_instr(INSTR_POP_VAR);
                emit_symbol(tmp);
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_expression(e);
                emit_instr(INSTR_UNTAG_OR_DIE);
                emit_int(target->tag);
                emit_target(target->tagged);
                emit_instr(INSTR_ASSIGN);
                break;
        default:
                emit_expression(e);
                emit_target(target);
                emit_instr(INSTR_ASSIGN);
        }
}

static void
emit_expression(struct expression const *e)
{
        state.loc = e->loc;
        add_location(e);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (e->local) {
                        emit_instr(INSTR_LOAD_VAR);
                } else {
                        emit_instr(INSTR_LOAD_REF);
                        addref(e->symbol);
                }
                emit_symbol(e->symbol);
                break;
        case EXPRESSION_MATCH:
                emit_match_expression(e);
                break;
        case EXPRESSION_TAG_APPLICATION:
                emit_expression(e->tagged);
                emit_instr(INSTR_TAG_PUSH);
                emit_int(e->tag);
                break;
        case EXPRESSION_RANGE:
                emit_expression(e->low);
                emit_expression(e->high);
                emit_instr(INSTR_RANGE);
                emit_int((e->flags & RANGE_EXCLUDE_LEFT) ? 1 : 0);
                emit_int((e->flags & RANGE_EXCLUDE_RIGHT) ? -1 : 0);
                break;
        case EXPRESSION_EQ:
                emit_assignment(e->target, e->value, 0);
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
                emit_int(e->tag);
                break;
        case EXPRESSION_REGEX:
                emit_instr(INSTR_REGEX);
                emit_symbol((uintptr_t) e->regex);
                emit_symbol((uintptr_t) e->extra);
                emit_symbol((uintptr_t) e->pattern);
                break;
        case EXPRESSION_ARRAY:
                for (int i = e->elements.count - 1; i >= 0; --i) {
                        emit_expression(e->elements.items[i]);
                }
                emit_instr(INSTR_ARRAY);
                emit_int(e->elements.count);
                break;
        case EXPRESSION_OBJECT:
                for (int i = e->keys.count - 1; i >= 0; --i) {
                        emit_expression(e->keys.items[i]);
                        emit_expression(e->values.items[i]);
                }
                emit_instr(INSTR_OBJECT);
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
                for (size_t i = 0; i < e->args.count; ++i) {
                        emit_expression(e->args.items[i]);
                }
                emit_expression(e->function);
                emit_instr(INSTR_CALL);
                emit_int(e->args.count);
                break;
        case EXPRESSION_METHOD_CALL:
                for (size_t i = 0; i < e->method_args.count; ++i) {
                        emit_expression(e->method_args.items[i]);
                }
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
                emit_instr(INSTR_KEYS);
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
                for (int i = 0; i < s->statements.count; ++i) {
                        emit_statement(s->statements.items[i]);
                }
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
                emit_assignment(s->target, s->value, 0);
                emit_instr(INSTR_POP);
                break;
        case STATEMENT_RETURN:
                if (state.function_depth == 0) {
                        fail("invalid 'return' statement (not inside of a function)");
                }
                if (s->return_value != NULL) {
                        emit_expression(s->return_value);
                } else {
                        emit_instr(INSTR_NIL);
                }
                for (int i = 0; i < state.bound_symbols.count; ++i) {
                        emit_instr(INSTR_POP_VAR);
                        emit_symbol(state.bound_symbols.items[i]);
                }
                emit_instr(INSTR_RETURN);
                break;
        case STATEMENT_BREAK:
                emit_instr(INSTR_JUMP);
                vec_push(state.breaks, state.code.count);
                emit_int(0);
                break;
        case STATEMENT_CONTINUE:
                emit_instr(INSTR_JUMP);
                vec_push(state.continues, state.code.count);
                emit_int(0);
                break;
        }
}

static void
emit_new_globals(void)
{
        for (int i = global_count; i < global->func_symbols.count; ++i) {
                if (global->func_symbols.items[i] >= builtin_count) {
                        emit_instr(INSTR_PUSH_VAR);
                        emit_symbol(global->func_symbols.items[i]);
                }
        }

        global_count = global->func_symbols.count;
}

static struct scope *
get_module_scope(char const *name)
{
        for (int i = 0; i < modules.count; ++i) {
                if (strcmp(name, modules.items[i].path) == 0) {
                        return modules.items[i].scope;
                }
        }

        return NULL;
}

static void
import_module(char *name, char *as)
{
        LOG("IMPORTING %s AS %s", name, as);

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
                if (strcmp(as, state.imports.items[i].name) == 0) {
                        fail("there is already a module imported under the name '%s'", as);
                }
                if (state.imports.items[i].scope == module_scope) {
                        fail("the module '%s' has already been imported", name);
                }
        }

        /*
         * If we've already generated code to load this module, we can skip to the part of the code
         * where we add the module to the current scope.
         */
        if (module_scope != NULL) {
                goto import;
        }

        char pathbuf[512];
        char const *home = getenv("HOME");
        if (home == NULL) {
                fail("unable to get $HOME from the environment");
        }

        snprintf(pathbuf, sizeof pathbuf, "%s/.plum/%s.plum", home, name);

        char *source = slurp(pathbuf);
        if (source == NULL) {
                fail("failed to read file: %s", pathbuf);
        }

        struct statement **p = parse(source);
        if (p == NULL) {
                fail("while importing module %s: %s", name, parse_error());
        }

        /*
         * Save the current compiler state so we can restore it after compiling
         * this module.
         */
        struct state save = state;
        state = freshstate();

        for (size_t i = 0; p[i] != NULL; ++i) {
                symbolize_statement(state.global, p[i]);
        }

        emit_new_globals();

        for (size_t i = 0; p[i] != NULL; ++i) {
                emit_statement(p[i]);
        }

        emit_instr(INSTR_HALT);

        /*
         * Add all of the location information from this module to the
         * global list.
         */
        patch_location_info();
        vec_push(location_lists, state.expression_locations);

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

        LOG("ADDING IMPORT WITH NAME: %s", as);
        vec_push(state.imports, ((struct import){ .name = as, .scope = module_scope }));
}

char const *
compiler_error(void)
{
        return err_msg;
}

void
compiler_init(void)
{
        symbol = 0;
        builtin_count = 0;
        global_count = 0;
        global = newscope(NULL, false);
        vec_init(public_symbols);
        vec_init(modules);

        tags_init();
        for (int i = 0; i < tagcount; ++i) {
                vec_push(global->identifiers, tags[i]);
                vec_push(global->symbols, tags_new(tags[i]));
        }

        state = freshstate();
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
                        s = newscope(NULL, false);
                        vec_push(modules, ((struct module){
                                .path = module,
                                .code = NULL,
                                .scope = s
                        }));
                }
        }

        addsymbol(s, name, false);
        builtin_count += 1;
}

char *
compiler_compile_source(char const *source, int *symbols, char const *filename)
{
        vec_init(state.code);
        vec_init(state.refs);
        vec_init(state.expression_locations);

        state.filename = filename;

        symbol = *symbols;

        struct statement **p = parse(source);
        if (p == NULL) {
                err_msg = parse_error();
                return NULL;
        }

        if (setjmp(jb) != 0) {
                *symbols = symbol;
                err_msg = err_buf;
                return NULL;
        }

        for (size_t i = 0; p[i] != NULL; ++i)
                symbolize_statement(state.global, p[i]);

        emit_new_globals();

        for (size_t i = 0; p[i] != NULL; ++i)
                emit_statement(p[i]);

        emit_instr(INSTR_HALT);

        add_location(NULL);
        patch_location_info();
        vec_push(location_lists, state.expression_locations);

        *symbols = symbol;
        return state.code.items;
}

struct location
compiler_get_location(char const *code, char const **file)
{
        location_vector *locs = NULL;

        uintptr_t c = (uintptr_t) code;

        /*
         * First do a linear search for the group of locations which
         * contains this one.
         */
        for (int i = 0; i < location_lists.count; ++i) {
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

        *file = locs->items[lo].e->filename;
        return locs->items[lo].e->loc;
}
