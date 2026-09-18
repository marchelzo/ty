#include <ctype.h>

#include "ast.h"
#include "scope.h"
#include "compiler.h"

#include "ty.h"

#define V(e) ((e) = visit_expression(ty, e, scope, ctxt))
#define VS(s) ((s) = visit_statement(ty, s, scope, ctxt))
#define VP(e) ((e) = visit_pattern(ty, e, scope, ctxt))
#define VT(t) ((t) = visit_type(ty, t, scope, ctxt))
#define VX(e) ((e) = type ? visit_type(ty, e, scope, ctxt) \
                          : visit_expression(ty, e, scope, ctxt))
#define VL(d, t) ((t) = visit_lvalue(ty, t, scope, ctxt, (d)))
#define VL_(t) ((t) = visit_lvalue(ty, t, scope, ctxt, decl))

#define SUB(f, name, ...) do {                           \
        Scope *tmp_scope = scope;                        \
        if (scope != NULL) {                             \
                scope = scope_new(ty, name, scope, f);   \
        }                                                \
        __VA_ARGS__;                                     \
        scope = tmp_scope;                               \
} while (0)

#define E1(e) ((e) = (ctxt->e_pre)(e, scope, ctxt->user))
#define E2(e) ((e) = (ctxt->e_post)(e, scope, ctxt->user))

#define T1(t) ((t) = (ctxt->t_pre)(t, scope, ctxt->user))
#define T2(t) ((t) = (ctxt->t_post)(t, scope, ctxt->user))

#define S1(s) ((s) = (ctxt->s_pre)(s, scope, ctxt->user))
#define S2(s) ((s) = (ctxt->s_post)(s, scope, ctxt->user))

#define P1(p) ((p) = (ctxt->p_pre)(p, scope, ctxt->user))
#define P2(p) ((p) = (ctxt->p_post)(p, scope, ctxt->user))

#define L1(t) ((t) = (ctxt->l_pre)(t, decl, scope, ctxt->user))
#define L2(t) ((t) = (ctxt->l_post)(t, decl, scope, ctxt->user))

static Expr *
id_e(Expr *e, Scope *scope, void *u)
{
        return e;
}

static Stmt *
id_s(Stmt *s, Scope *scope, void *u)
{
        return s;
}

static Expr *
id_l(Expr *t, bool decl, Scope *scope, void *u)
{
        return t;
}

VisitorCtx
visit_identity(Ty *ty)
{
        return (VisitorCtx) {
                id_e, id_e,
                id_e, id_e,
                id_e, id_e,
                id_l, id_l,
                id_s, id_s,
                NULL
        };
}

static void
bind_name(Ty *ty, Scope *scope, char const *name, u32 flags)
{
        if (scope == NULL || name == NULL || s_eq(name, "_")) {
                return;
        }

        Symbol *existing = scope_local_lookup(ty, scope, name);
        if (existing != NULL) {
                existing->flags |= flags;
                return;
        }

        Symbol sym = {
                .i      = -1,
                .symbol = -1,
                .class  = -1,
                .tag    = -1,
                .flags  = flags
        };

        scope_insert_as(ty, scope, &sym, name);
}

static void
bind_scope(Ty *ty, Scope *dst, Scope const *src)
{
        for (usize i = 0; i < src->size; ++i) {
                for (Symbol *sym = src->table[i]; sym != NULL; sym = sym->next) {
                        if (scope_local_lookup(ty, dst, sym->identifier) == NULL) {
                                scope_insert(ty, dst, sym);
                        }
                }
        }
}

static Scope *
visit_namespace(Ty *ty, Scope *scope, Namespace const *ns)
{
        if (scope == NULL || ns == NULL || !ScopeIsModule(scope)) {
                return scope;
        }

        Scope *parent = visit_namespace(ty, scope, ns->next);
        Symbol *sym = scope_local_lookup(ty, parent, ns->id);
        if (SymbolIsNamespace(sym)) {
                return sym->scope;
        }

        Symbol var = {
                .i      = -1,
                .symbol = -1,
                .class  = -1,
                .tag    = -1,
                .flags  = SYM_NAMESPACE,
                .scope  = scope_new(ty, ns->id, parent, false)
        };
        var.scope->flags |= SCOPE_NAMESPACE;
        scope_insert_as(ty, parent, &var, ns->id);

        return var.scope;
}

static void
bind_regex(Ty *ty, Scope *scope, Regex const *re)
{
        if (scope == NULL) {
                return;
        }

        u32 n;
        u32 width;
        PCRE2_SPTR names;
        pcre2_pattern_info(re->pcre2, PCRE2_INFO_NAMECOUNT, &n);
        pcre2_pattern_info(re->pcre2, PCRE2_INFO_NAMEENTRYSIZE, &width);
        pcre2_pattern_info(re->pcre2, PCRE2_INFO_NAMETABLE, &names);

        for (u32 i = 0; i <= re->ncap; ++i) {
                char id[16];
                ty_snprintf(id, sizeof id, "$%u", i);
                for (u32 j = 0; j < n; ++j) {
                        PCRE2_SPTR entry = names + j * width;
                        if (((entry[0] << 8) | entry[1]) == i) {
                                bind_name(ty, scope, (char const *)(entry + 2), 0);
                                goto NextCapture;
                        }
                }
                bind_name(ty, scope, sclonea(ty, id), 0);
NextCapture:
                ;
        }
}

static void
visit_params(Ty *ty, ExprVec *params, Scope *scope, VisitorCtx *ctxt)
{
        for (usize i = 0; i < vN(*params); ++i) {
                Expr *param = v__(*params, i);
                bind_name(ty, scope, param->identifier, SYM_TYPE_VAR);
                VT(v__(*params, i));
        }
}

static void
visit_function(Ty *ty, Expr *e, Scope *scope, VisitorCtx *ctxt)
{
        for (usize i = 0; i < vN(e->decorators); ++i) {
                V(v__(e->decorators, i));
        }

        SUB(true, e->name == NULL ? "(anon)" : e->name,
                bind_name(ty, scope, e->name, SYM_FUNCTION | SYM_CONST);
                visit_params(ty, &e->type_params, scope, ctxt);
                for (usize i = 0; i < vN(e->params); ++i) {
                        V(v__(e->dflts, i));
                        bind_name(ty, scope, v__(e->params, i), 0);
                }
                for (usize i = 0; i < vN(e->constraints); ++i) {
                        VT(v__(e->constraints, i));
                }
                if (e->type != EXPRESSION_MULTI_FUNCTION) {
                        VT(e->return_type);
                        for (usize i = 0; i < vN(e->type_bounds); ++i) {
                                VT(v_(e->type_bounds, i)->var);
                                VT(v_(e->type_bounds, i)->bound);
                        }
                }
                for (usize i = 0; i < vN(e->functions); ++i) {
                        V(v__(e->functions, i));
                }
                VS(e->body);
        );
}

static void
bind_members(Ty *ty, ExprVec const *members, Scope *scope, u32 flags)
{
        for (usize i = 0; i < vN(*members); ++i) {
                Expr *m = v__(*members, i);
                char const *name;
                if (m->type == EXPRESSION_EQ) {
                        m = m->target;
                }
                switch (m->type) {
                case EXPRESSION_IDENTIFIER:
                        name = m->identifier;
                        break;
                case EXPRESSION_FUNCTION:
                case EXPRESSION_IMPLICIT_FUNCTION:
                case EXPRESSION_MULTI_FUNCTION:
                case EXPRESSION_GENERATOR:
                        name = m->name;
                        break;
                default:
                        continue;
                }
                bind_name(ty, scope, name, SYM_MEMBER | flags);
        }
}

static void
visit_members(Ty *ty, ExprVec *members, Scope *scope, VisitorCtx *ctxt)
{
        for (usize i = 0; i < vN(*members); ++i) {
                Expr **m = v_(*members, i);
                switch ((*m)->type) {
                case EXPRESSION_IDENTIFIER:
                        VL(true, *m);
                        break;
                case EXPRESSION_EQ:
                        V((*m)->value);
                        VL(true, (*m)->target);
                        break;
                default:
                        V(*m);
                        break;
                }
        }
}

static void
visit_class(Ty *ty, ClassDefinition *cd, Scope *scope, VisitorCtx *ctxt)
{
        SUB(false, cd->name,
                visit_params(ty, &cd->type_params, scope, ctxt);
                VT(cd->super);
                for (usize i = 0; i < vN(cd->traits); ++i) {
                        VT(v__(cd->traits, i));
                }

                bind_members(ty, &cd->s_fields, scope, SYM_STATIC);
                bind_members(ty, &cd->s_methods, scope, SYM_STATIC | SYM_FUNCTION);
                bind_members(ty, &cd->s_getters, scope, SYM_STATIC | SYM_PROPERTY);
                bind_members(ty, &cd->s_setters, scope, SYM_STATIC | SYM_PROPERTY);
                visit_members(ty, &cd->s_fields, scope, ctxt);

                SUB(false, "(static methods)",
                        bind_name(ty, scope, "self", 0);
                        visit_members(ty, &cd->s_methods, scope, ctxt);
                        visit_members(ty, &cd->s_getters, scope, ctxt);
                        visit_members(ty, &cd->s_setters, scope, ctxt);
                );

                SUB(false, "(instance)",
                        bind_members(ty, &cd->fields, scope, 0);
                        bind_members(ty, &cd->methods, scope, SYM_FUNCTION);
                        bind_members(ty, &cd->getters, scope, SYM_PROPERTY);
                        bind_members(ty, &cd->setters, scope, SYM_PROPERTY);
                        visit_members(ty, &cd->fields, scope, ctxt);
                        bind_name(ty, scope, "self", 0);
                        visit_members(ty, &cd->methods, scope, ctxt);
                        visit_members(ty, &cd->getters, scope, ctxt);
                        visit_members(ty, &cd->setters, scope, ctxt);
                );
        );
}

static void
visit_part(Ty *ty, struct condpart *p, Scope *scope, VisitorCtx *ctxt)
{
        V(p->e);
        if (p->def) {
                VP(p->target);
        } else {
                VL(false, p->target);
        }
}

static Scope *
visit_comprehension(Ty *ty, Comprehension *parts, Scope *scope, VisitorCtx *ctxt)
{
        for (usize i = 0; i < vN(*parts); ++i) {
                ComprPart *part = v_(*parts, i);
                V(part->iter);
                if (scope != NULL) {
                        scope = scope_new(ty, "(comprehension)", scope, false);
                }
                VL(true, part->pattern);
                VS(part->where);
                V(part->_while);
                V(part->_if);
        }

        return scope;
}

static void
visit_statements(Ty *ty, StmtVec *stmts, Scope *scope, VisitorCtx *ctxt)
{
        usize end = 0;
        bool top = ScopeIsModule(scope) || ScopeIsNamespace(scope);

        for (usize i = 0; i < vN(*stmts); ++i) {
                for (end = max(end, i); end < vN(*stmts); ++end) {
                        Stmt *s = v__(*stmts, end);
                        Scope *bound = visit_namespace(ty, scope, s->ns);
                        switch (s->type) {
                        case STATEMENT_FUNCTION_DEFINITION:
                        case STATEMENT_OPERATOR_DEFINITION:
                        case STATEMENT_MACRO_DEFINITION:
                        case STATEMENT_FUN_MACRO_DEFINITION:
                        case STATEMENT_PATTERN_DEFINITION:
                                bind_name(ty, bound, s->target->identifier, SYM_FUNCTION | SYM_CONST);
                                break;
                        case STATEMENT_CLASS_DEFINITION:
                        case STATEMENT_TAG_DEFINITION:
                        case STATEMENT_TYPE_DEFINITION:
                                if (top) {
                                        bind_name(ty, bound, s->class.name, SYM_CONST);
                                        break;
                                }
                                goto Visit;
                        case STATEMENT_DEFINITION:
                                if (top) {
                                        VisitorCtx decls = visit_identity(ty);
                                        (void)visit_lvalue(ty, s->target, bound, &decls, true);
                                        break;
                                }
                        default:
                                if (!top) {
                                        goto Visit;
                                }
                                break;
                        }
                }
Visit:
                VS(v__(*stmts, i));
        }
}

Stmt *
visit_statement(Ty *ty, Stmt *s, Scope *scope, VisitorCtx *ctxt)
{
        if (s == NULL) {
                return NULL;
        }

        if (IsExpr(s)) {
                return (Stmt *)visit_expression(ty, (Expr *)s, scope, ctxt);
        }

        scope = visit_namespace(ty, scope, s->ns);
        S1(s);

        switch (s->type) {
        case STATEMENT_RETURN:
        case STATEMENT_GENERATOR_RETURN:
                for (int i = 0; i < s->returns.count; ++i) {
                        V(s->returns.items[i]);
                }
                break;
        case STATEMENT_MULTI:
                visit_statements(ty, &s->statements, scope, ctxt);
                break;
        case STATEMENT_BLOCK:
                SUB(false, "(block)",
                        visit_statements(ty, &s->statements, scope, ctxt);
                );
                break;
        case STATEMENT_EXPRESSION:
        case STATEMENT_DEFER:
        case STATEMENT_BREAK:
                V(s->expression);
                break;
        case STATEMENT_WHILE:
                SUB(false, "(while)",
                        for (usize i = 0; i < vN(s->_while.parts); ++i) {
                                visit_part(ty, v__(s->_while.parts, i), scope, ctxt);
                        }
                        VS(s->_while.block);
                );
                break;
        case STATEMENT_IF:
                if (s->_if.neg) {
                        VS(s->_if.then);
                        for (usize i = 0; i < vN(s->_if.parts); ++i) {
                                visit_part(ty, v__(s->_if.parts, i), scope, ctxt);
                        }
                        SUB(false, "(if-not)", VS(s->_if._else));
                } else {
                        SUB(false, "(if)",
                                for (usize i = 0; i < vN(s->_if.parts); ++i) {
                                        visit_part(ty, v__(s->_if.parts, i), scope, ctxt);
                                }
                                VS(s->_if.then);
                        );
                        SUB(false, "(else)", VS(s->_if._else));
                }
                break;
        case STATEMENT_WHILE_MATCH:
        case STATEMENT_MATCH:
                V(s->match.e);
                for (int i = 0; i < s->match.patterns.count; ++i) {
                        SUB(false, "(match)",
                                VP(s->match.patterns.items[i]);
                                VS(s->match.statements.items[i]);
                        );
                }
                break;
        case STATEMENT_TRY:
        {
                VS(s->try.s);

                for (int i = 0; i < s->try.patterns.count; ++i) {
                        SUB(false, "(catch)",
                                VP(s->try.patterns.items[i]);
                                VS(s->try.handlers.items[i]);
                        );
                }

                VS(s->try.finally);

                break;

        }
        case STATEMENT_EACH_LOOP:
                V(s->each.array);
                SUB(false, "(each)",
                        VL(true, s->each.target);
                        V(s->each._if);
                        V(s->each._while);
                        VS(s->each.body);
                );
                break;
        case STATEMENT_FOR_LOOP:
                SUB(false, "(for)",
                        VS(s->for_loop.init);
                        V(s->for_loop.cond);
                        V(s->for_loop.next);
                        SUB(false, "(for-body)", VS(s->for_loop.body));
                );
                break;
        case STATEMENT_DEFINITION:
                V(s->value);
                VL(true, s->target);
                if (s->cnst && s->target->type == EXPRESSION_IDENTIFIER) {
                        bind_name(ty, scope, s->target->identifier, SYM_CONST);
                }
                break;
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_OPERATOR_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
        case STATEMENT_PATTERN_DEFINITION:
                VL(true, s->target);
                V(s->value);
                break;
        case STATEMENT_CLASS_DEFINITION:
        case STATEMENT_TAG_DEFINITION:
                bind_name(ty, scope, s->class.name, SYM_CONST);
                visit_class(ty, &s->class, scope, ctxt);
                break;
        case STATEMENT_TYPE_DEFINITION:
                bind_name(ty, scope, s->class.name, SYM_TYPE_ALIAS | SYM_CONST);
                SUB(false, s->class.name,
                        visit_params(ty, &s->class.type_params, scope, ctxt);
                        VT(s->class.type);
                );
                break;
        case STATEMENT_SET_TYPE:
                VL(false, s->target);
                VT(s->value);
                break;
        case STATEMENT_IMPORT:
                bind_name(ty, scope, s->import.as, SYM_CONST);
                if (!s->import.hiding) {
                        for (usize i = 0; i < vN(s->import.aliases); ++i) {
                                bind_name(ty, scope, v__(s->import.aliases, i), SYM_CONST);
                        }
                }
                break;
        case STATEMENT_USE:
                if (vN(s->use.names) == 0 && vN(s->use.name) > 0) {
                        bind_name(ty, scope, v_L(s->use.name), SYM_CONST);
                }
                for (usize i = 0; i < vN(s->use.names); ++i) {
                        bind_name(ty, scope, v__(s->use.names, i), SYM_CONST);
                }
                break;
        }

        return S2(s);
}

Expr *
visit_pattern(Ty *ty, Expr *p, Scope *scope, VisitorCtx *ctxt)
{
        if (p == NULL) {
                return NULL;
        }

        P1(p);

        switch (p->type) {
        case EXPRESSION_IDENTIFIER:
                if (p->module != NULL) {
                        V(p);
                        break;
                }
                if (isupper((unsigned char)p->identifier[0])) {
                        for (Scope *s = scope; s != NULL; s = s->parent) {
                                Symbol *sym = scope_local_lookup(ty, s, p->identifier);
                                if (sym == NULL) {
                                        continue;
                                }
                                if (!SymbolIsConst(sym)) {
                                        break;
                                }
                                V(p);
                                return P2(p);
                        }
                }
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
                bind_name(ty, scope, p->identifier, 0);
                VT(p->constraint);
                break;

        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_ALIAS_PATTERN:
                bind_name(ty, scope, p->identifier, 0);
                VT(p->constraint);
                VP(p->tagged);
                break;

        case EXPRESSION_SPREAD:
                VP(p->value);
                break;

        case EXPRESSION_REF_PATTERN:
        case EXPRESSION_REF_MAYBE_PATTERN:
                VL(false, p->target);
                break;

        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                V(p->left);
                VP(p->right);
                break;

        case EXPRESSION_CHECK_MATCH:
                VP(p->left);
                V(p->right);
                break;

        case EXPRESSION_KW_AND:
                VP(p->left);
                for (usize i = 0; i < vN(p->p_cond); ++i) {
                        visit_part(ty, v__(p->p_cond, i), scope, ctxt);
                }
                break;

        case EXPRESSION_ARRAY:
                for (usize i = 0; i < vN(p->elements); ++i) {
                        VP(v__(p->elements, i));
                }
                break;

        case EXPRESSION_DICT:
                V(p->dflt);
                for (usize i = 0; i < vN(p->keys); ++i) {
                        V(v__(p->keys, i));
                        VP(v__(p->values, i));
                }
                break;

        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (usize i = 0; i < vN(p->es); ++i) {
                        VP(v__(p->es, i));
                }
                break;

        case EXPRESSION_CHOICE_PATTERN:
        {
                Scope *shared = NULL;
                if (scope != NULL) {
                        shared = scope_new(ty, "(choices)", scope, false);
                }
                for (usize i = 0; i < vN(p->es); ++i) {
                        SUB(false, "(choice)",
                                VP(v__(p->es, i));
                                if (shared != NULL) {
                                        bind_scope(ty, shared, scope);
                                }
                        );
                }
                if (shared != NULL) {
                        bind_scope(ty, scope, shared);
                }
                break;
        }

        case EXPRESSION_REGEX:
                bind_regex(ty, scope, p->regex);
                V(p);
                break;

        case EXPRESSION_FUNCTION_CALL:
                V(p->function);
                goto Arguments;

        case EXPRESSION_TAG_PATTERN_CALL:
                VP(p->function);
Arguments:
                for (usize i = 0; i < vN(p->args); ++i) {
                        VP(v__(p->args, i));
                }
                for (usize i = 0; i < vN(p->kwargs); ++i) {
                        VP(v__(p->kwargs, i));
                }
                break;

        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_OBJECT_PATTERN:
                VP(p->tagged);
                break;

        case EXPRESSION_METHOD_CALL:
                V(p->object);
                for (usize i = 0; i < vN(p->method_args); ++i) {
                        VP(v__(p->method_args, i));
                }
                for (usize i = 0; i < vN(p->method_kwargs); ++i) {
                        VP(v__(p->method_kwargs, i));
                }
                break;

        default:
                V(p);
                break;
        }

        return P2(p);
}

Expr *
visit_lvalue(Ty *ty, Expr *t, Scope *scope, VisitorCtx *ctxt, bool decl)
{
        if (t == NULL) {
                return NULL;
        }

        L1(t);

        switch (t->type) {
        case EXPRESSION_TAG_PATTERN:
                VL_(t->tagged);
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
                if (decl) {
                        bind_name(ty, scope, t->identifier, 0);
                }
                VT(t->constraint);
                break;

        case EXPRESSION_SPREAD:
                VL_(t->value);
                break;

        case EXPRESSION_REF_PATTERN:
        case EXPRESSION_REF_MAYBE_PATTERN:
                VL(false, t->target);
                break;

        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                V(t->left);
                VL_(t->right);
                break;

        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_OBJECT_PATTERN:
                VL_(t->tagged);
                break;

        case EXPRESSION_FUNCTION_CALL:
                V(t->function);
                goto Arguments;

        case EXPRESSION_TAG_PATTERN_CALL:
                VL_(t->function);
Arguments:
                for (usize i = 0; i < vN(t->args); ++i) {
                        VL_(v__(t->args, i));
                }
                for (usize i = 0; i < vN(t->kwargs); ++i) {
                        VL_(v__(t->kwargs, i));
                }
                break;

        case EXPRESSION_METHOD_CALL:
                V(t->object);
                for (usize i = 0; i < vN(t->method_args); ++i) {
                        VL_(v__(t->method_args, i));
                }
                for (usize i = 0; i < vN(t->method_kwargs); ++i) {
                        VL_(v__(t->method_kwargs, i));
                }
                break;

        case EXPRESSION_ARRAY:
                for (usize i = 0; i < t->elements.count; ++i) {
                        VL_(v__(t->elements, i));
                }
                break;

        case EXPRESSION_DICT:
                V(t->dflt);
                for (int i = 0; i < t->keys.count; ++i) {
                        V(t->keys.items[i]);
                        VL_(t->values.items[i]);
                }
                break;

        case EXPRESSION_SUBSCRIPT:
                V(t->container);
                V(t->subscript);
                break;

        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                V(t->object);
                break;

        case EXPRESSION_DYN_MEMBER_ACCESS:
                V(t->object);
                V(t->member);
                break;

        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
                for (int i = 0; i < t->es.count; ++i) {
                        VL_(t->es.items[i]);
                }
                break;

        default:
                V(t);
        }

        return L2(t);
}

static void
visit_children(Ty *ty, Expr *e, Scope *scope, VisitorCtx *ctxt, bool type)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_PACK:
                VT(e->constraint);
                break;

        case EXPRESSION_COMPILE_TIME:
                VX(e->operand);
                break;

        case EXPRESSION_SPECIAL_STRING:
                V(e->lang);
                for (usize i = 0; i < vN(e->fmts); ++i) {
                        V(v__(e->fmts, i));
                }
                for (usize i = 0; i < vN(e->fmtfs); ++i) {
                        V(v__(e->fmtfs, i));
                }
        case EXPRESSION_DYNAMIC_REGEX:
                for (int i = 0; i < e->expressions.count; ++i) {
                        V(e->expressions.items[i]);
                }
                break;

        case EXPRESSION_TAG:
                break;

        case EXPRESSION_TAG_APPLICATION:
                VX(e->tagged);
                break;

        case EXPRESSION_MATCH:
                VX(e->subject);
                for (int i = 0; i < e->patterns.count; ++i) {
                        SUB(false, "(match)",
                                VP(e->patterns.items[i]);
                                VX(e->thens.items[i]);
                        );
                }
                break;

        case EXPRESSION_USER_OP:
                VX(e->sc);
        case EXPRESSION_PLUS:
        case EXPRESSION_MINUS:
        case EXPRESSION_STAR:
        case EXPRESSION_DIV:
        case EXPRESSION_PERCENT:
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
        case EXPRESSION_XOR:
        case EXPRESSION_SHR:
        case EXPRESSION_SHL:
        case EXPRESSION_KW_OR:
        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
                VX(e->left);
                VX(e->right);
                break;

        case EXPRESSION_AND:
        case EXPRESSION_OR:
                VX(e->left);
                SUB(false, "(short-circuit)", VX(e->right));
                break;

        case EXPRESSION_KW_AND:
                VX(e->left);
                for (int i = 0; i < vN(e->p_cond); ++i) {
                        visit_part(ty, v__(e->p_cond, i), scope, ctxt);
                }
                break;

        case EXPRESSION_DEFINED:
        case EXPRESSION_IFDEF:
                break;

        case EXPRESSION_EVAL:
        case EXPRESSION_UNARY_OP:
        case EXPRESSION_UNSAFE:
        case EXPRESSION_PREFIX_HASH:
        case EXPRESSION_PREFIX_BANG:
        case EXPRESSION_PREFIX_QUESTION:
        case EXPRESSION_PREFIX_MINUS:
        case EXPRESSION_PREFIX_AT:
        case EXPRESSION_PREFIX_INC:
        case EXPRESSION_PREFIX_DEC:
        case EXPRESSION_POSTFIX_INC:
        case EXPRESSION_POSTFIX_DEC:
        case EXPRESSION_ENTER:
                VX(e->operand);
                break;

        case EXPRESSION_TYPE_OF:
                V(e->operand);
                break;

        case EXPRESSION_FUNCTION_TYPE:
                VT(e->left);
                VT(e->right);
                break;

        case EXPRESSION_TYPE:
                VT(e->constraint);
                break;

        case EXPRESSION_CAST:
                VX(e->left);
                VT(e->right);
                break;

        case EXPRESSION_CONDITIONAL:
                SUB(false, "(then)",
                        VX(e->cond);
                        VX(e->then);
                );
                SUB(false, "(else)", VX(e->_else));
                break;

        case EXPRESSION_STATEMENT:
                VS(e->statement);
                break;

        case EXPRESSION_TEMPLATE:
                for (usize i = 0; i < vN(e->template.exprs); ++i) {
                        V(v__(e->template.exprs, i));
                }
                for (usize i = 0; i < vN(e->template.holes); ++i) {
                        V(v__(e->template.holes, i));
                }
                for (usize i = 0; i < vN(e->template.stmts); ++i) {
                        VS(v__(e->template.stmts, i));
                }
                break;

        case EXPRESSION_FUNCTION_CALL:
                VX(e->function);
                for (usize i = 0; i < vN(e->args); ++i) {
                        VX(v__(e->args, i));
                }
                for (usize i = 0;  i < vN(e->fconds); ++i) {
                        VX(v__(e->fconds, i));
                }
                for (usize i = 0; i < vN(e->kwargs); ++i) {
                        VX(v__(e->kwargs, i));
                }
                for (usize i = 0; i < vN(e->fkwconds); ++i) {
                        VX(v__(e->fkwconds, i));
                }
                break;

        case EXPRESSION_SUBSCRIPT:
                VX(e->container);
                VX(e->subscript);
                break;

        case EXPRESSION_SLICE:
                VX(e->slice.e);
                VX(e->slice.i);
                VX(e->slice.j);
                VX(e->slice.k);
                break;

        case EXPRESSION_DYN_MEMBER_ACCESS:
                VX(e->member);
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                VX(e->object);
                break;

        case EXPRESSION_DYN_METHOD_CALL:
                VX(e->method);
        case EXPRESSION_METHOD_CALL:
                VX(e->object);
                for (usize i = 0; i < e->method_args.count; ++i) {
                        VX(e->method_args.items[i]);
                }
                for (usize i = 0; i < e->mconds.count; ++i) {
                        VX(e->mconds.items[i]);
                }
                for (usize i = 0; i < e->method_kwargs.count; ++i) {
                        VX(e->method_kwargs.items[i]);
                }
                break;

        case EXPRESSION_EQ:
        case EXPRESSION_MAYBE_EQ:
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MINUS_EQ:
        case EXPRESSION_MOD_EQ:
        case EXPRESSION_AND_EQ:
        case EXPRESSION_OR_EQ:
        case EXPRESSION_XOR_EQ:
        case EXPRESSION_SHL_EQ:
        case EXPRESSION_SHR_EQ:
                VX(e->value);
                VL(false, e->target);
                break;

        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_FUNCTION:
                visit_function(ty, e, scope, ctxt);
                break;

        case EXPRESSION_WITH:
                SUB(false, "(with)",
                        VS(e->with.block);
                );
                for (usize i = 0; i < vN(e->with.defs); ++i) {
                        v__(e->with.defs, i) = v__(e->with.block->statements, i);
                }
                break;

        case EXPRESSION_THROW:
                VX(e->throw);
                break;

        case EXPRESSION_YIELD:
                for (int i = 0; i < e->es.count; ++i) {
                        VX(e->es.items[i]);
                }
                break;

        case EXPRESSION_ARRAY:
                for (usize i = 0; i < e->elements.count; ++i) {
                        SUB(false, "(array item)",
                                VX(e->aconds.items[i]);
                                VX(e->elements.items[i]);
                        );
                }
                break;

        case EXPRESSION_ARRAY_COMPR:
        {
                Scope *outer = scope;
                scope = visit_comprehension(ty, &e->compr, scope, ctxt);
                for (usize i = 0; i < e->elements.count; ++i) {
                        VX(e->elements.items[i]);
                        VX(e->aconds.items[i]);
                }
                scope = outer;
                break;
        }

        case EXPRESSION_DICT:
                VX(e->dflt);
                for (usize i = 0; i < e->keys.count; ++i) {
                        VX(e->keys.items[i]);
                        VX(e->values.items[i]);
                }
                break;

        case EXPRESSION_DICT_COMPR:
        {
                VX(e->dflt);
                Scope *outer = scope;
                scope = visit_comprehension(ty, &e->dcompr, scope, ctxt);
                for (usize i = 0; i < vN(e->keys); ++i) {
                        VX(v__(e->keys, i));
                        VX(v__(e->values, i));
                }
                scope = outer;
                break;
        }

        case EXPRESSION_TYPE_UNION:
                for (int i = 0; i < e->es.count; ++i) {
                        VT(e->es.items[i]);
                }
                break;

        case EXPRESSION_LIST:
                for (int i = 0; i < e->es.count; ++i) {
                        VX(e->es.items[i]);
                }
                break;

        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        VX(e->es.items[i]);
                        VX(e->tconds.items[i]);
                }
                break;

        case EXPRESSION_SPREAD:
        case EXPRESSION_SPLAT:
                VX(e->value);
                break;

        case EXPRESSION_MACRO_INVOCATION:
                break;

        }
}

Expr *
visit_expression(Ty *ty, Expr *e, Scope *scope, VisitorCtx *ctxt)
{
        if (e == NULL) {
                return NULL;
        }

        if (IsStmt(e)) {
                return (Expr *)visit_statement(ty, (Stmt *)e, scope, ctxt);
        }

        E1(e);
        visit_children(ty, e, scope, ctxt, false);
        return E2(e);
}

Expr *
visit_type(Ty *ty, Expr *e, Scope *scope, VisitorCtx *ctxt)
{
        if (e == NULL) {
                return NULL;
        }

        T1(e);
        visit_children(ty, e, scope, ctxt, true);
        return T2(e);
}

/* vim: set sw=8 sts=8 expandtab: */
