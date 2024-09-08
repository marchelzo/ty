#include "ast.h"

#define V(e) ((e) = visit_expression(e, hooks))
#define VS(s) ((s) = visit_statement(s, hooks))
#define VP(e) ((e) = visit_pattern(e, hooks))
#define VL(t) ((t) = visit_lvalue(t, hooks))

#define E1(e) ((e) = (hooks->e_pre)(e, hooks->user))
#define E2(e) ((e) = (hooks->e_post)(e, hooks->user))

#define S1(s) ((s) = (hooks->s_pre)(s, hooks->user))
#define S2(s) ((s) = (hooks->s_post)(s, hooks->user))

#define P1(p) ((p) = (hooks->p_pre)(p, hooks->user))
#define P2(p) ((p) = (hooks->p_post)(p, hooks->user))

#define L1(t) ((t) = (hooks->l_pre)(t, hooks->user))
#define L2(t) ((t) = (hooks->l_post)(t, hooks->user))

static Expr *id_e(Expr *e, void *u) { return e; }
static Stmt *id_s(Stmt *s, void *u) { return s; }

VisitorSet
visit_identitiy(void)
{
        return (VisitorSet) {
                id_e, id_e,
                id_e, id_e,
                id_e, id_e,
                id_s, id_s,
                NULL
        };
}

Stmt *
visit_statement(Stmt *s, VisitorSet const *hooks)
{
        S1(s);

        switch (s->type) {
        case STATEMENT_RETURN:
                for (int i = 0; i < s->returns.count; ++i) {
                        V(s->returns.items[i]);
                }
                break;
        case STATEMENT_MULTI:
                for (size_t i = 0; i < s->statements.count; ++i) {
                        VS(s->statements.items[i]);
                }
                break;
        case STATEMENT_EXPRESSION:
                V(s->expression);
                break;
        }

        return S2(s);
}

Expr *
visit_pattern(Expr *p, VisitorSet const *hooks)
{
        return visit_expression(p, hooks);
}

Expr *
visit_lvalue(Expr *t, VisitorSet const *hooks)
{
        return visit_expression(t, hooks);
}

Expr *
visit_expression(Expr *e, VisitorSet const *hooks)
{
        if (e == NULL)
                return NULL;

        E1(e);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                break;
        case EXPRESSION_COMPILE_TIME:
                V(e->operand);
                break;
        case EXPRESSION_SPECIAL_STRING:
                for (int i = 0; i < e->expressions.count; ++i)
                        V(e->expressions.items[i]);
                break;
        case EXPRESSION_TAG:
                break;
        case EXPRESSION_TAG_APPLICATION:
                V(e->tagged);
                break;
        case EXPRESSION_MATCH:
                V(e->subject);
                for (int i = 0; i < e->patterns.count; ++i) {
                        if (e->patterns.items[i]->type == EXPRESSION_LIST) {
                                for (int j = 0; j < e->patterns.items[i]->es.count; ++j) {
                                        V(e->patterns.items[i]->es.items[j]);
                                }
                        } else {
                                V(e->patterns.items[i]);
                        }
                        V(e->thens.items[i]);
                }
                break;
        case EXPRESSION_USER_OP:
                V(e->sc);
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
                V(e->left);
                V(e->right);
                break;
        case EXPRESSION_DEFINED:
                /*
                e->type = EXPRESSION_BOOLEAN;
                if (e->module != NULL) {
                        struct scope *mscope = search_import_scope(e->module);
                        e->boolean = mscope != NULL && scope_lookup(mscope, e->identifier) != NULL;
                } else {
                        e->boolean = scope_lookup(scope, e->identifier) != NULL;
                }
                */
                break;
        case EXPRESSION_IFDEF:
                /*
                if (e->module != NULL) {
                        struct scope *mscope = search_import_scope(e->module);
                        if (mscope != NULL && scope_lookup(mscope, e->identifier) != NULL) {
                                e->type = EXPRESSION_IDENTIFIER;
                                V(e);
                                e->type = EXPRESSION_IFDEF;
                        } else {
                                e->type = EXPRESSION_NIL;
                        }
                } else {
                        if (scope_lookup(scope, e->identifier) != NULL) {
                                e->type = EXPRESSION_IDENTIFIER;
                                V(e);
                                e->type = EXPRESSION_IFDEF;
                        } else {
                                e->type = EXPRESSION_NONE;
                        }
                }
                */
                break;
        case EXPRESSION_EVAL:
        case EXPRESSION_PREFIX_HASH:
        case EXPRESSION_PREFIX_BANG:
        case EXPRESSION_PREFIX_QUESTION:
        case EXPRESSION_PREFIX_MINUS:
        case EXPRESSION_PREFIX_AT:
        case EXPRESSION_PREFIX_INC:
        case EXPRESSION_PREFIX_DEC:
        case EXPRESSION_POSTFIX_INC:
        case EXPRESSION_POSTFIX_DEC:
                V(e->operand);
                break;
        case EXPRESSION_CONDITIONAL:
                V(e->cond);
                V(e->then);
                V(e->otherwise);
                break;
        case EXPRESSION_STATEMENT:
                VS(e->statement);
                break;
        case EXPRESSION_TEMPLATE:
                for (size_t i = 0; i < e->template.exprs.count; ++i) {
                        V(e->template.exprs.items[i]);
                }
                break;
        case EXPRESSION_FUNCTION_CALL:
                V(e->function);
                for (size_t i = 0;  i < e->args.count; ++i)

                        V(e->args.items[i]);
                for (size_t i = 0;  i < e->args.count; ++i)
                        V(e->fconds.items[i]);
                for (size_t i = 0; i < e->kwargs.count; ++i)
                        V(e->kwargs.items[i]);
                break;
        case EXPRESSION_SUBSCRIPT:
                V(e->container);
                V(e->subscript);
                break;
        case EXPRESSION_MEMBER_ACCESS:
                V(e->object);
                break;
        case EXPRESSION_METHOD_CALL:
                V(e->object);
                for (size_t i = 0;  i < e->method_args.count; ++i)
                        V(e->method_args.items[i]);
                for (size_t i = 0;  i < e->method_args.count; ++i)
                        V(e->mconds.items[i]);
                for (size_t i = 0; i < e->method_kwargs.count; ++i)
                        V(e->method_kwargs.items[i]);
                break;
        case EXPRESSION_EQ:
        case EXPRESSION_MAYBE_EQ:
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MINUS_EQ:
                V(e->value);
                VL(e->target);
                break;
        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_FUNCTION:
                for (int i = 0; i < e->decorators.count; ++i) {
                        V(e->decorators.items[i]);
                }

                for (size_t i = 0; i < e->params.count; ++i) {
                        V(e->dflts.items[i]);
                }

                for (size_t i = 0; i < e->params.count; ++i) {
                        V(e->constraints.items[i]);
                }

                V(e->return_type);

                VS(e->body);

                break;
        case EXPRESSION_WITH:
                VS(e->with.block);
                // FIXME: do anything with e->with.defs?
                break;
        case EXPRESSION_THROW:
                V(e->throw);
                break;
        case EXPRESSION_YIELD:
                for (int i = 0; i < e->es.count; ++i) {
                    V(e->es.items[i]);
                }
                break;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i) {
                        V(e->elements.items[i]);
                        V(e->aconds.items[i]);
                }
                break;
        case EXPRESSION_ARRAY_COMPR:
                V(e->compr.iter);
                VL(e->compr.pattern); /* true, false */
                V(e->compr.cond);
                for (size_t i = 0; i < e->elements.count; ++i) {
                        V(e->elements.items[i]);
                        V(e->aconds.items[i]);
                }
                break;
        case EXPRESSION_DICT:
                V(e->dflt);
                for (size_t i = 0; i < e->keys.count; ++i) {
                        V(e->keys.items[i]);
                        V(e->values.items[i]);
                }
                break;
        case EXPRESSION_DICT_COMPR:
                V(e->dcompr.iter);
                VL(e->dcompr.pattern); /* true, false */
                V(e->dcompr.cond);
                for (size_t i = 0; i < e->keys.count; ++i) {
                        V(e->keys.items[i]);
                        V(e->values.items[i]);
                }
                break;
        case EXPRESSION_LIST:
                for (int i = 0; i < e->es.count; ++i) {
                        V(e->es.items[i]);
                }
                break;
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        V(e->es.items[i]);
                        V(e->tconds.items[i]);
                }
                break;
        case EXPRESSION_SPREAD:
        case EXPRESSION_SPLAT:
                V(e->value);
                break;
        case EXPRESSION_MACRO_INVOCATION:
                break;
        }

        return E2(e);
}
