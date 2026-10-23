#include <stdlib.h>
#include <string.h>

#include <pcre2.h>
#include <pthread.h>

#include "ty.h"
#include "ast.h"
#include "token.h"
#include "lex.h"
#include "value.h"
#include "vm.h"
#include "functions.h"
#include "compiler.h"
#include "syntax.h"
#include "parse.h"
#include "scope.h"
#include "types2.h"
#include "types2_core.h"
#include "class.h"
#include "intern.h"

#define X(t) #t
static char const *ExprKinds[] = { TY_EXPRESSION_TYPES };
static char const *StmtKinds[] = { TY_STATEMENT_TYPES };
#undef X

typedef struct {
        Expr *e;
        i32 parent;
        bool target;
        bool shared;
        bool alias;
} SpanNode;

typedef struct {
        void **slots;
        usize cap;
        usize n;
} PtrSet;

typedef struct {
        Ty *ty;
        vec(SpanNode) nodes;
        vec(i32) stack;
        PtrSet targets;
        PtrSet seen;
        PtrSet xholes;
        PtrSet decorators;
        i32 alias;
} SpanWalk;

typedef struct {
        i32 parent;
        Expr const *e;
} Sibling;

typedef struct {
        char const *src;
        usize n;
        u8 *starts;
        u8 *ends;
        Array *out;
        Module const *mod;
} SpanCheck;

static char const *
kind_name(Expr const *e)
{
        if (e->type < EXPRESSION_MAX_TYPE) {
                return ExprKinds[e->type];
        }

        if (e->type > STATEMENT_TYPE_START) {
                return StmtKinds[e->type - STATEMENT_TYPE_START - 1];
        }

        return "?";
}

inline static usize
pset_hash(void const *p, usize cap)
{
        return ((uptr)p >> 4) * 0x9E3779B97F4A7C15ULL & (cap - 1);
}

static bool
pset_has(PtrSet const *set, void const *p)
{
        if (set->cap == 0) {
                return false;
        }

        usize mask = set->cap - 1;

        for (usize h = pset_hash(p, set->cap); set->slots[h] != NULL; h = (h + 1) & mask) {
                if (set->slots[h] == p) {
                        return true;
                }
        }

        return false;
}

static void
pset_add(Ty *ty, PtrSet *set, void *p);

static void
pset_grow(Ty *ty, PtrSet *set)
{
        PtrSet old = *set;

        set->cap   = (old.cap == 0) ? 1024 : 2 * old.cap;
        set->slots = smA0(set->cap * sizeof (void *));
        set->n     = 0;

        for (usize i = 0; i < old.cap; ++i) {
                if (old.slots[i] != NULL) {
                        pset_add(ty, set, old.slots[i]);
                }
        }
}

static void
pset_add(Ty *ty, PtrSet *set, void *p)
{
        if (2 * (set->n + 1) > set->cap) {
                pset_grow(ty, set);
        }

        usize h = pset_hash(p, set->cap);

        while (set->slots[h] != NULL) {
                if (set->slots[h] == p) {
                        return;
                }
                h = (h + 1) & (set->cap - 1);
        }

        set->slots[h] = p;
        set->n += 1;
}

static i32
top(SpanWalk const *w)
{
        for (isize i = vN(w->stack) - 1; i >= 0; --i) {
                if (v__(w->stack, i) >= 0) {
                        return v__(w->stack, i);
                }
        }

        return -1;
}

static void
enter(SpanWalk *w, Expr *e)
{
        Ty *ty = w->ty;
        i32 parent = top(w);

        if (
                (e != NULL)
             && (parent >= 0)
             && pset_has(&w->decorators, e)
             && (v__(w->nodes, parent).e->type == EXPRESSION_FUNCTION)
        ) {
                parent = v__(w->nodes, parent).parent;
                if (parent >= 0 && v__(w->nodes, parent).e->type == STATEMENT_FUNCTION_DEFINITION) {
                        parent = v__(w->nodes, parent).parent;
                }
        }

        if (e == NULL || (parent >= 0 && v__(w->nodes, parent).e == e)) {
                svP(w->stack, -1);
                return;
        }

        bool alias = (w->alias > 0) || (
                pset_has(&w->xholes, e)
             && (parent >= 0)
             && (v__(w->nodes, parent).e->type == EXPRESSION_TEMPLATE)
        );

        SpanNode node = {
                .e      = e,
                .parent = parent,
                .target = alias || pset_has(&w->targets, e),
                .shared = !alias && pset_has(&w->seen, e),
                .alias  = alias
        };

        if (alias) {
                w->alias += 1;
        } else {
                pset_add(ty, &w->seen, e);
        }

        svP(w->nodes, node);
        svP(w->stack, (i32)vN(w->nodes) - 1);
}

static void
leave(SpanWalk *w)
{
        i32 i = vXx(w->stack);

        if (i >= 0 && v__(w->nodes, i).alias) {
                w->alias -= 1;
        }
}

static bool
is_hole(Expr const *e)
{
        switch (e->type) {
        case EXPRESSION_TEMPLATE_HOLE:
        case EXPRESSION_TEMPLATE_VHOLE:
        case EXPRESSION_TEMPLATE_THOLE:
                return true;

        default:
                return false;
        }
}

static i32
enclosing_template(SpanWalk const *w, i32 i)
{
        for (i = v__(w->nodes, i).parent; i >= 0; i = v__(w->nodes, i).parent) {
                if (v__(w->nodes, i).e->type == EXPRESSION_TEMPLATE) {
                        return i;
                }
        }

        return -1;
}

static bool
contains_ptr(ExprVec const *xs, Expr const *x)
{
        for (usize i = 0; i < vN(*xs); ++i) {
                if (v__(*xs, i) == x) {
                        return true;
                }
        }

        return false;
}

static bool
encloses(Expr const *outer, Expr const *inner)
{
        return (outer->start.byte <= inner->start.byte)
            && (inner->end.byte <= outer->end.byte);
}

static bool
descends_from(SpanWalk const *w, i32 i, i32 ancestor)
{
        for (; i >= 0; i = v__(w->nodes, i).parent) {
                if (i == ancestor) {
                        return true;
                }
        }

        return false;
}

static i32
smallest_container(SpanWalk const *w, i32 root, i32 j)
{
        Expr const *e = v__(w->nodes, j).e;
        i32 best = root;

        for (i32 k = root + 1; k < vN(w->nodes); ++k) {
                SpanNode const *node = v_(w->nodes, k);
                if (
                        (k == j)
                     || node->target
                     || !encloses(node->e, e)
                     || !descends_from(w, k, root)
                     || descends_from(w, k, j)
                ) {
                        continue;
                }
                Expr const *b = v__(w->nodes, best).e;
                if (node->e->end.byte - node->e->start.byte <= b->end.byte - b->start.byte) {
                        best = k;
                }
        }

        return best;
}

static void
adopt_hole_contents(SpanWalk *w)
{
        for (i32 i = 0; i < vN(w->nodes); ++i) {
                SpanNode const *hole = v_(w->nodes, i);
                if (!is_hole(hole->e) || hole->target) {
                        continue;
                }
                i32 t = enclosing_template(w, i);
                if (t < 0) {
                        continue;
                }
                Expr const *tmpl = v__(w->nodes, t).e;
                if (xF(hole->e, hole).i >= vN(xF(tmpl, template).holes)) {
                        continue;
                }
                Expr const *content = v__(xF(tmpl, template).holes, xF(hole->e, hole).i);
                for (i32 j = t + 1; j < vN(w->nodes); ++j) {
                        SpanNode *node = v_(w->nodes, j);
                        if (j != i && node->e == content && !node->target) {
                                node->parent = i;
                                break;
                        }
                }
        }

        for (i32 j = 0; j < vN(w->nodes); ++j) {
                SpanNode *node = v_(w->nodes, j);
                if (node->parent < 0 || node->target) {
                        continue;
                }
                Expr const *tmpl = v__(w->nodes, node->parent).e;
                if (
                        (tmpl->type != EXPRESSION_TEMPLATE)
                     || !contains_ptr(&xF(tmpl, template).holes, node->e)
                ) {
                        continue;
                }
                node->parent = smallest_container(w, node->parent, j);
        }
}

static Expr *
pre_e(Expr *e, Scope *scope, void *u)
{
        SpanWalk *w = u;
        Ty *ty = w->ty;

        if (e != NULL && e->type == EXPRESSION_TEMPLATE) {
                for (usize i = 0; i < vN(xF(e, template).exprs); ++i) {
                        pset_add(ty, &w->xholes, v__(xF(e, template).exprs, i));
                }
        }

        if (e != NULL && e->type == EXPRESSION_FUNCTION) {
                for (usize i = 0; i < vN(xF(e, decorators)); ++i) {
                        pset_add(ty, &w->decorators, v__(xF(e, decorators), i));
                }
        }

        enter(w, e);

        return e;
}

static Expr *
post_e(Expr *e, Scope *scope, void *u)
{
        leave(u);
        return e;
}

static Expr *
pre_l(Expr *e, bool def, Scope *scope, void *u)
{
        enter(u, e);
        return e;
}

static Expr *
post_l(Expr *e, bool def, Scope *scope, void *u)
{
        leave(u);
        return e;
}

static Stmt *
pre_s(Stmt *s, Scope *scope, void *u)
{
        SpanWalk *w = u;
        Ty *ty = w->ty;

        switch (s->type) {
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_OPERATOR_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
                pset_add(ty, &w->targets, sF(s, target));
                break;
        }

        enter(w, (Expr *)s);

        return s;
}

static Stmt *
post_s(Stmt *s, Scope *scope, void *u)
{
        leave(u);
        return s;
}

static bool
in_source(SpanCheck const *c, Expr const *e)
{
        return (LocS(e->start) >= c->src)
            && (LocS(e->end) >= c->src)
            && (LocS(e->start) <= c->src + c->n)
            && (LocS(e->end) <= c->src + c->n)
            && (e->start.byte <= c->n)
            && (e->end.byte <= c->n);
}

static bool
in_macro(SpanCheck const *c, Expr const *e)
{
        if (c->mod == NULL) {
                return false;
        }

        for (isize i = 0; i < vN(c->mod->macros); ++i) {
                MacroSpan const *m = v_(c->mod->macros, i);
                if (m->start.byte <= e->start.byte && e->end.byte <= m->end.byte) {
                        return true;
                }
        }

        return false;
}

static bool
macro_output(SpanCheck const *c, Expr const *e)
{
        if (c->mod == NULL) {
                return false;
        }

        for (isize i = 0; i < vN(c->mod->macros); ++i) {
                Expr const *x = v_(c->mod->macros, i)->expansion;
                if (x == NULL) {
                        continue;
                }
                if (
                        (x == e)
                     || (
                                (x->type == STATEMENT_EXPRESSION)
                             && (sF(((Stmt const *)x), expression) == e)
                        )
                ) {
                        return true;
                }
        }

        return false;
}

static void
report(Ty *ty, SpanCheck *c, char const *check, Expr const *e, Expr const *other)
{
        Value v = vTn(
                "check",  xSz(check),
                "kind",   xSz(kind_name(e)),
                "start",  INTEGER(e->start.byte),
                "end",    INTEGER(e->end.byte),
                "line",   INTEGER(LocLine(e->start) + 1),
                "other",  (other == NULL) ? NIL : xSz(kind_name(other))
        );

        vAp(c->out, v);
}

static int
by_parent_start(void const *a, void const *b)
{
        Sibling const *x = a;
        Sibling const *y = b;

        if (x->parent != y->parent) {
                return (x->parent < y->parent) ? -1 : 1;
        }

        if (x->e->start.byte != y->e->start.byte) {
                return (x->e->start.byte < y->e->start.byte) ? -1 : 1;
        }

        if (x->e->end.byte != y->e->end.byte) {
                return (x->e->end.byte < y->e->end.byte) ? -1 : 1;
        }

        return 0;
}

static bool
checkable(SpanCheck const *c, SpanNode const *node)
{
        return !node->target
            && !node->shared
            && in_source(c, node->e)
            && (node->e->start.byte <= node->e->end.byte);
}

static void
check_node(Ty *ty, SpanCheck *c, SpanWalk const *w, i32 i)
{
        SpanNode const *node = v_(w->nodes, i);
        Expr const *e = node->e;
        SpanNode const *parent = (node->parent >= 0) ? v_(w->nodes, node->parent) : NULL;

        if (node->target) {
                return;
        }

        if (node->shared) {
                report(ty, c, "shared", e, NULL);
                return;
        }

        if (!in_source(c, e)) {
                if (
                        (parent == NULL || in_source(c, parent->e))
                     && (parent == NULL || !in_macro(c, parent->e))
                     && !macro_output(c, e)
                ) {
                        report(ty, c, "foreign", (parent == NULL) ? e : parent->e, e);
                }
                return;
        }

        if (e->start.byte > e->end.byte) {
                report(ty, c, "inverted", e, NULL);
                return;
        }

        if (e->start.byte < e->end.byte) {
                if (!c->starts[e->start.byte]) {
                        report(ty, c, "start-not-token", e, NULL);
                }
                if (!c->ends[e->end.byte]) {
                        report(ty, c, "end-not-token", e, NULL);
                }
        }

        if (
                (parent != NULL)
             && checkable(c, parent)
             && (
                        (e->start.byte < parent->e->start.byte)
                     || (e->end.byte > parent->e->end.byte)
                )
        ) {
                report(ty, c, "escapes-parent", e, parent->e);
        }
}

static void
check_siblings(Ty *ty, SpanCheck *c, SpanWalk const *w)
{
        vec(Sibling) kids = {0};

        for (i32 i = 0; i < vN(w->nodes); ++i) {
                SpanNode const *node = v_(w->nodes, i);
                if (checkable(c, node) && node->e->start.byte < node->e->end.byte) {
                        svP(kids, ((Sibling) { node->parent, node->e }));
                }
        }

        qsort(vv(kids), vN(kids), sizeof (Sibling), by_parent_start);

        for (isize i = 1; i < vN(kids); ++i) {
                Sibling const *a = v_(kids, i - 1);
                Sibling const *b = v_(kids, i);
                if (a->parent != b->parent) {
                        continue;
                }
                if (
                        (a->e->start.byte == b->e->start.byte)
                     && (a->e->end.byte == b->e->end.byte)
                ) {
                        report(ty, c, "same-span", b->e, a->e);
                } else if (a->e->end.byte > b->e->start.byte) {
                        report(ty, c, "sibling-overlap", b->e, a->e);
                }
        }
}

static void
mark_tokens(Ty *ty, SpanCheck *c, TokenVector const *tokens)
{
        for (isize i = 0; i < vN(*tokens); ++i) {
                Token const *t = v_(*tokens, i);
                if (
                        (t->ctx == LEX_FAKE)
                     || (t->type == TOKEN_END)
                     || (t->start.byte >= t->end.byte)
                     || (t->end.byte > c->n)
                ) {
                        continue;
                }
                c->starts[t->start.byte] = true;
                c->ends[t->end.byte] = true;
        }
}

static void
walk_module(Ty *ty, Module *mod, SpanWalk *w)
{
        VisitorCtx visitor = visit_identity(ty);
        visitor.e_pre  = pre_e;
        visitor.e_post = post_e;
        visitor.t_pre  = pre_e;
        visitor.t_post = post_e;
        visitor.p_pre  = pre_e;
        visitor.p_post = post_e;
        visitor.l_pre  = pre_l;
        visitor.l_post = post_l;
        visitor.s_pre  = pre_s;
        visitor.s_post = post_s;
        visitor.user   = w;

        for (int i = 0; mod->prog != NULL && mod->prog[i] != NULL; ++i) {
                visit_statement(ty, mod->prog[i], NULL, &visitor);
        }

        adopt_hole_contents(w);
}

static void
walk_node(Ty *ty, Expr *e, SpanWalk *w)
{
        VisitorCtx visitor = visit_identity(ty);
        visitor.e_pre  = pre_e;
        visitor.e_post = post_e;
        visitor.t_pre  = pre_e;
        visitor.t_post = post_e;
        visitor.p_pre  = pre_e;
        visitor.p_post = post_e;
        visitor.l_pre  = pre_l;
        visitor.l_post = post_l;
        visitor.s_pre  = pre_s;
        visitor.s_post = post_s;
        visitor.user   = w;

        if (IsStmt(e)) {
                visit_statement(ty, (Stmt *)e, NULL, &visitor);
        } else {
                visit_expression(ty, e, NULL, &visitor);
        }
}

// ty/syntax.walk(mod: Module) -> Array[{
//     kind: String,
//     start: Int,
//     end: Int,
//     parent: Int,
//     excluded: Bool,
//     synth: Bool
// }]
TY_BUILTIN_RAW(ty_syntax_walk)
{
        ASSERT_ARGC("ty.syntax.walk()", 1);

        Module *mod = ARGx(0, VALUE_MODULE).mod;

        SCRATCH_SAVE();

        SpanWalk w = { .ty = ty };
        walk_module(ty, mod, &w);

        Array *out = vA();

        gP(&ARRAY(out));

        for (i32 i = 0; i < vN(w.nodes); ++i) {
                SpanNode const *node = v_(w.nodes, i);
                vAp(out, vTn(
                        "kind",     xSz(kind_name(node->e)),
                        "start",    INTEGER(node->e->start.byte),
                        "end",      INTEGER(node->e->end.byte),
                        "parent",   INTEGER(node->parent),
                        "excluded", BOOLEAN(node->target || node->shared),
                        "synth",    BOOLEAN(node->e->synth)
                ));
        }

        gX();

        SCRATCH_RESTORE();

        return ARRAY(out);
}

// ty/syntax.check(mod: Module) -> Array[{
//     check: String,
//     kind: String,
//     start: Int,
//     end: Int,
//     line: Int,
//     other: String | nil
// }]
TY_BUILTIN_RAW(ty_syntax_check)
{
        ASSERT_ARGC("ty.syntax.check()", 1);

        Module *mod = ARGx(0, VALUE_MODULE).mod;

        SCRATCH_SAVE();

        SpanWalk w = { .ty = ty };
        SpanCheck c = {
                .src = mod->source,
                .n   = strlen(mod->source),
                .out = vA(),
                .mod = mod
        };

        c.starts = smA0(c.n + 1);
        c.ends   = smA0(c.n + 1);

        mark_tokens(ty, &c, &mod->tokens);

        for (isize i = 0; i < vN(mod->macros); ++i) {
                MacroSpan const *m = v_(mod->macros, i);
                if (m->start.byte < m->end.byte && m->end.byte <= c.n) {
                        c.starts[m->start.byte] = true;
                        c.ends[m->end.byte] = true;
                }
        }

        walk_module(ty, mod, &w);

        gP(&ARRAY(c.out));

        for (i32 i = 0; i < vN(w.nodes); ++i) {
                check_node(ty, &c, &w, i);
        }

        check_siblings(ty, &c, &w);

        gX();

        SCRATCH_RESTORE();

        return ARRAY(c.out);
}

typedef struct {
        SyntaxNode node;
        i32 rank;
        i32 order;
} Pending;

static int
by_extent(void const *a, void const *b)
{
        Pending const *x = a;
        Pending const *y = b;

        if (x->node.start != y->node.start) {
                return (x->node.start < y->node.start) ? -1 : 1;
        }

        if (x->node.end != y->node.end) {
                return (x->node.end > y->node.end) ? -1 : 1;
        }

        if (x->rank != y->rank) {
                return (x->rank < y->rank) ? -1 : 1;
        }

        return (x->order < y->order) ? -1 : (x->order > y->order);
}

static bool
keep_in_tree(SpanCheck const *c, SpanNode const *node)
{
        Expr const *e = node->e;

        switch (e->type) {
        case EXPRESSION_STATEMENT:
        case STATEMENT_EXPRESSION:
                return false;
        }

        return !node->alias
            && !node->shared
            && in_source(c, e)
            && (e->start.byte < e->end.byte || e->synth);
}

static i32
extra_kind(char const *kind)
{
        static struct {
                char const *name;
                i32 kind;
        } const kinds[] = {
                { "Paren",     SYNTAX_PAREN     },
                { "Sugar",     SYNTAX_SUGAR     },
                { "Param",     SYNTAX_PARAM     },
                { "Kwarg",     SYNTAX_KWARG     },
                { "Condition", SYNTAX_CONDITION },
                { "Namespace", SYNTAX_NAMESPACE },
                { "Embedded",  SYNTAX_EMBEDDED  },
                { "Region",    SYNTAX_REGION    }
        };

        for (usize i = 0; i < countof(kinds); ++i) {
                if (strcmp(kinds[i].name, kind) == 0) {
                        return kinds[i].kind;
                }
        }

        return 0;
}

static i32
rank_of(i32 kind)
{
        switch (kind) {
        case SYNTAX_MACRO:
        case SYNTAX_PP_REGION:
        case SYNTAX_NAMESPACE:
                return 0;

        case SYNTAX_EMBEDDED:
        case SYNTAX_REGION:
                return 1;

        case SYNTAX_SUGAR:
                return 2;

        case SYNTAX_PAREN:
                return 3;

        case SYNTAX_PARAM:
        case SYNTAX_KWARG:
        case SYNTAX_CONDITION:
                return 4;

        default:
                return 5;
        }
}

static void
add_pending(Ty *ty, void *pending, SyntaxNode node, i32 order)
{
        vec(Pending) *p = pending;
        svP(*p, ((Pending) { .node = node, .rank = rank_of(node.kind), .order = order }));
}

static void
add_pp_regions(Ty *ty, Module const *mod, usize n, void *pending)
{
        vec(u32) stack = {0};

        for (isize i = 0; i + 1 < vN(mod->tokens); ++i) {
                Token const *t = v_(mod->tokens, i);
                Token const *u = v_(mod->tokens, i + 1);
                if (t->type != TOKEN_DIRECTIVE || !t->pp) {
                        continue;
                }
                if (
                        (u->type == TOKEN_KEYWORD)
                     && (u->keyword == KEYWORD_IF || u->keyword == KEYWORD_WHILE)
                ) {
                        svP(stack, t->start.byte);
                } else if (u->type == ']' && vN(stack) > 0 && u->end.byte <= n) {
                        SyntaxNode node = {
                                .kind   = SYNTAX_PP_REGION,
                                .start  = vXx(stack),
                                .end    = u->end.byte,
                                .parent = -1
                        };
                        add_pending(ty, pending, node, -1);
                }
        }
}

void
syntax_snapshot(Ty *ty, Module *mod)
{
        if (mod->source == NULL) {
                return;
        }

        SCRATCH_SAVE();

        SpanWalk w = { .ty = ty };
        SpanCheck c = { .src = mod->source, .n = strlen(mod->source) };

        walk_module(ty, mod, &w);

        SpanWalk embedded = { .ty = ty };
        PtrSet expansion = {0};

        for (isize k = 0; k < vN(mod->macros); ++k) {
                Expr *x = (Expr *)v_(mod->macros, k)->expansion;
                if (x != NULL) {
                        SpanWalk out = { .ty = ty };
                        walk_node(ty, x, &out);
                        for (i32 i = 0; i < vN(out.nodes); ++i) {
                                pset_add(ty, &expansion, v_(out.nodes, i)->e);
                        }
                }
        }

        for (isize k = 0; k < vN(mod->extras); ++k) {
                Expr *x = (Expr *)v_(mod->extras, k)->node;
                if (x != NULL && !pset_has(&w.seen, x)) {
                        walk_node(ty, x, &embedded);
                }
        }

        vec(Pending) pending = {0};
        PtrSet added = {0};

        SpanWalk const *walks[] = { &w, &embedded };

        for (usize k = 0; k < countof(walks); ++k) {
                for (i32 i = 0; i < vN(walks[k]->nodes); ++i) {
                        SpanNode const *node = v_(walks[k]->nodes, i);
                        if (!keep_in_tree(&c, node) || pset_has(&added, node->e)) {
                                continue;
                        }
                        pset_add(ty, &added, node->e);
                        SyntaxNode s = {
                                .kind   = node->e->type,
                                .start  = node->e->start.byte,
                                .end    = node->e->end.byte,
                                .parent = -1,
                                .e      = node->e,
                                .synth  = node->e->synth || (
                                        (k == 0)
                                     && pset_has(&expansion, node->e)
                                )
                        };
                        add_pending(ty, &pending, s, (i32)(k * 1000000) + i);
                }
        }

        for (isize k = vN(mod->extras) - 1; k >= 0; --k) {
                SyntaxExtra const *x = v_(mod->extras, k);
                if (!x->inner) {
                        continue;
                }
                for (isize i = 0; i < vN(pending); ++i) {
                        SyntaxNode *node = &v_(pending, i)->node;
                        if (node->start == x->start.byte && node->end == x->end.byte) {
                                node->start = x->inner_start.byte;
                                node->end = x->inner_end.byte;
                        }
                }
        }

        for (isize k = 0; k < vN(mod->extras); ++k) {
                SyntaxExtra const *x = v_(mod->extras, k);
                i32 kind = extra_kind(x->kind);
                if (
                        (kind == 0)
                     || (LocS(x->start) < mod->source)
                     || (LocS(x->start) > mod->source + c.n)
                     || (x->end.byte > c.n)
                     || (x->start.byte >= x->end.byte)
                ) {
                        continue;
                }
                SyntaxNode s = {
                        .kind   = kind,
                        .start  = x->start.byte,
                        .end    = x->end.byte,
                        .parent = -1,
                        .form   = x->form
                };
                add_pending(ty, &pending, s, -1);
        }

        for (isize k = 0; k < vN(mod->macros); ++k) {
                MacroSpan const *m = v_(mod->macros, k);
                if (
                        (strcmp(m->name, "$$[") == 0)
                     || (LocS(m->start) < mod->source)
                     || (LocS(m->start) > mod->source + c.n)
                     || (m->end.byte > c.n)
                     || (m->start.byte >= m->end.byte)
                ) {
                        continue;
                }
                SyntaxNode s = {
                        .kind   = SYNTAX_MACRO,
                        .start  = m->start.byte,
                        .end    = m->end.byte,
                        .parent = -1,
                        .form   = m->name
                };
                add_pending(ty, &pending, s, -1);
        }

        add_pp_regions(ty, mod, c.n, &pending);

        qsort(vv(pending), vN(pending), sizeof (Pending), by_extent);

        vec(i32) stack = {0};

        v00(mod->syntax);

        for (isize i = 0; i < vN(pending); ++i) {
                SyntaxNode node = v_(pending, i)->node;

                while (
                        (vN(stack) > 0)
                     && (v_(mod->syntax, *vvL(stack))->end <= node.start)
                     && !(node.start == node.end && v_(mod->syntax, *vvL(stack))->end == node.start)
                ) {
                        vN(stack) -= 1;
                }

                if (
                        (vN(stack) > 0)
                     && (v_(mod->syntax, *vvL(stack))->end < node.end)
                ) {
                        continue;
                }

                node.parent = (vN(stack) > 0) ? *vvL(stack) : -1;

                avP(mod->syntax, node);
                svP(stack, (i32)vN(mod->syntax) - 1);
        }

        mod->has_syntax = true;

        SCRATCH_RESTORE();
}

static char const *
syntax_kind_name(i32 kind)
{
        switch (kind) {
        case SYNTAX_PAREN:     return "Paren";
        case SYNTAX_SUGAR:     return "Sugar";
        case SYNTAX_PARAM:     return "Param";
        case SYNTAX_KWARG:     return "Kwarg";
        case SYNTAX_CONDITION: return "Condition";
        case SYNTAX_NAMESPACE: return "Namespace";
        case SYNTAX_MACRO:     return "MacroInvocation";
        case SYNTAX_PP_REGION: return "PpRegion";
        case SYNTAX_EMBEDDED:  return "Embedded";
        case SYNTAX_REGION:    return "Region";
        }

        Expr const probe = { .type = kind };

        return kind_name(&probe);
}

// ty/syntax.nodes(mod: Module) -> Array[{
//     kind: String,
//     stmt: Bool,
//     start: Int,
//     end: Int,
//     parent: Int,
//     form: String | nil,
//     synth: Bool
// }]
TY_BUILTIN_RAW(ty_syntax_nodes)
{
        ASSERT_ARGC("ty.syntax.nodes()", 1);

        Module *mod = ARGx(0, VALUE_MODULE).mod;

        if (!mod->has_syntax) {
                syntax_snapshot(ty, mod);
        }

        Array *out = vA();

        gP(&ARRAY(out));

        for (isize i = 0; i < vN(mod->syntax); ++i) {
                SyntaxNode const *node = v_(mod->syntax, i);
                vAp(out, vTn(
                        "kind",   xSz(syntax_kind_name(node->kind)),
                        "stmt",   BOOLEAN(node->kind > STATEMENT_TYPE_START),
                        "start",  INTEGER(node->start),
                        "end",    INTEGER(node->end),
                        "parent", INTEGER(node->parent),
                        "form",   (node->form == NULL) ? NIL : vSsz(node->form),
                        "synth",  BOOLEAN(node->synth)
                ));
        }

        gX();

        return ARRAY(out);
}

// ty/syntax.macros(mod: Module) -> Array[{name: String, start: Int, end: Int}]
TY_BUILTIN_RAW(ty_syntax_macros)
{
        ASSERT_ARGC("ty.syntax.macros()", 1);

        Module *mod = ARGx(0, VALUE_MODULE).mod;
        usize n = (mod->source == NULL) ? 0 : strlen(mod->source);
        Array *out = vA();

        gP(&ARRAY(out));

        for (isize i = 0; i < vN(mod->macros); ++i) {
                MacroSpan const *m = v_(mod->macros, i);
                if (
                        (LocS(m->start) < mod->source)
                     || (LocS(m->start) > mod->source + n)
                     || (m->end.byte > n)
                     || (m->start.byte >= m->end.byte)
                ) {
                        continue;
                }
                vAp(out, vTn(
                        "name",  vSsz(m->name),
                        "start", INTEGER(m->start.byte),
                        "end",   INTEGER(m->end.byte)
                ));
        }

        gX();

        return ARRAY(out);
}

// ty/syntax.kinds() -> {expressions: Array[String], statements: Array[String]}
TY_BUILTIN_RAW(ty_syntax_kinds)
{
        ASSERT_ARGC("ty.syntax.kinds()", 0);

        Array *exprs = vA();
        Array *stmts = vA();

        gP(&ARRAY(exprs));
        gP(&ARRAY(stmts));

        for (usize i = 0; i < countof(ExprKinds); ++i) {
                vAp(exprs, xSz(ExprKinds[i]));
        }

        for (usize i = 0; i < countof(StmtKinds); ++i) {
                vAp(stmts, xSz(StmtKinds[i]));
        }

        Value out = vTn("expressions", ARRAY(exprs), "statements", ARRAY(stmts));

        gX();
        gX();

        return out;
}

// ty/syntax.extras(mod: Module) -> Array[{kind: String, form: String | nil, start: Int, end: Int}]
TY_BUILTIN_RAW(ty_syntax_extras)
{
        ASSERT_ARGC("ty.syntax.extras()", 1);

        Module *mod = ARGx(0, VALUE_MODULE).mod;
        usize n = (mod->source == NULL) ? 0 : strlen(mod->source);
        Array *out = vA();

        gP(&ARRAY(out));

        for (isize i = 0; i < vN(mod->extras); ++i) {
                SyntaxExtra const *x = v_(mod->extras, i);
                if (
                        (LocS(x->start) < mod->source)
                     || (LocS(x->start) > mod->source + n)
                     || (x->end.byte > n)
                     || (x->start.byte >= x->end.byte)
                ) {
                        continue;
                }
                vAp(out, vTn(
                        "kind",  xSz(x->kind),
                        "form",  (x->form == NULL) ? NIL : xSz(x->form),
                        "start", INTEGER(x->start.byte),
                        "end",   INTEGER(x->end.byte)
                ));
        }

        gX();

        return ARRAY(out);
}

typedef struct {
        Array *kind;
        Array *form;
        Array *kstart;
        Array *kcount;
        Array *kids;
        Array *ostart;
        Array *ocount;
        Array *own;
        Array *text;
        Array *punct;
        Array *ftok;
        Array *ltok;
        Array *hole;
        Array *seq;
        Array *tokhole;
        Array *kinds;
        Array *deep;
        Array *alts;
        Array *gaps;
        Array *roots;
        Array *slotmap;
        Array *mode;
        Array *lnum;
        Array *tnum;
        Array *lnl;
        Array *tnl;
        Array *lcm;
        Array *tcm;
        Array *lspc;
        Array *tspc;
        Array *tstart;
        Array *tend;
        Array *llen;
        Array *tlen;
        Array *ref;
        Array *callee;
        Array *ty;
        Array *tyhole;
        Array *tymode;
        Array *sem;
} Packed;

enum {
        PACKED_FIELDS = 40
};

enum {
        TYPE_HOLE_NONE,
        TYPE_HOLE_STRICT,
        TYPE_HOLE_GRADUAL
};

enum {
        GAP_ANY,
        GAP_NONE,
        GAP_SPACE,
        GAP_NEWLINE,
        GAP_BLANK,
        GAP_BIND,
        GAP_REGEX,
        GAP_COMMENT,
        GAP_COMMENT_BIND,
        GAP_COMMENT_REGEX,
        GAP_COMMENT_TEXT
};

typedef struct {
        i64 type;
        i64 a;
        i64 b;
        i64 c;
} SynBind;

typedef vec(Packed) PackedVec;
typedef vec(i64) I64Vec;

typedef struct {
        Ty *ty;
        char const *src;
        Packed const *p;
        Packed s;
        PackedVec subs;
        i64 paren;
        vec(SynBind) binds;
        I64Vec trail;
        I64Vec tokmap;
        I64Vec lastmap;
        I64Vec tails;
} SynMatch;

inline static i64
at(Array const *a, i64 i)
{
        return v__(*a, i).z;
}

inline static i64
len(Array const *a)
{
        return (a == NULL) ? 0 : (i64)vN(*a);
}

static Array *
field(Value const *v, usize i)
{
        if (v->type != VALUE_ARRAY || i >= vN(*v->array)) {
                return NULL;
        }

        Value const *f = v_(*v->array, i);

        return (f->type == VALUE_ARRAY) ? f->array : NULL;
}

static void
unpack(Value const *v, Packed *p)
{
        Array **fields = (Array **)p;

        for (usize i = 0; i < PACKED_FIELDS; ++i) {
                fields[i] = field(v, i);
        }
}

inline static i64
kid(Packed const *p, i64 n, i64 i)
{
        return at(p->kids, at(p->kstart, n) + i);
}

inline static i64
nkids(Packed const *p, i64 n)
{
        return at(p->kcount, n);
}

static i64
unparen(SynMatch const *m, Packed const *p, i64 n)
{
        while (at(p->kind, n) == m->paren && nkids(p, n) == 1) {
                n = kid(p, n, 0);
        }

        return n;
}

inline static i64
opt(Array const *a, i64 i)
{
        return (a == NULL || i < 0 || i >= len(a)) ? -1 : at(a, i);
}

static bool
same_tree(SynMatch const *m, i64 a, i64 b)
{
        Packed const *s = &m->s;

        a = unparen(m, s, a);
        b = unparen(m, s, b);

        if (opt(s->ref, a) >= 0 && opt(s->ref, b) >= 0) {
                return opt(s->ref, a) == opt(s->ref, b);
        }

        if (
                (at(s->ftok, a) == at(s->ltok, a))
             && (at(s->ftok, b) == at(s->ltok, b))
             && (at(s->ftok, a) >= 0)
             && (at(s->ftok, b) >= 0)
             && (at(s->text, at(s->ftok, a)) == at(s->text, at(s->ftok, b)))
        ) {
                return true;
        }

        if (
                (at(s->kind, a) != at(s->kind, b))
             || (at(s->form, a) != at(s->form, b))
             || (nkids(s, a) != nkids(s, b))
        ) {
                return false;
        }

        i64 i = at(s->ostart, a);
        i64 j = at(s->ostart, b);
        i64 ie = i + at(s->ocount, a);
        i64 je = j + at(s->ocount, b);

        for (;;) {
                while (i < ie && at(s->punct, at(s->own, i))) {
                        i += 1;
                }
                while (j < je && at(s->punct, at(s->own, j))) {
                        j += 1;
                }
                if (i == ie || j == je) {
                        break;
                }
                if (at(s->text, at(s->own, i)) != at(s->text, at(s->own, j))) {
                        return false;
                }
                i += 1;
                j += 1;
        }

        if (i != ie || j != je) {
                return false;
        }

        for (i64 k = 0; k < nkids(s, a); ++k) {
                if (!same_tree(m, kid(s, a, k), kid(s, b, k))) {
                        return false;
                }
        }

        return true;
}

static bool
same_bind(SynMatch const *m, SynBind const *x, SynBind const *y)
{
        Packed const *s = &m->s;

        if (x->type == 1 && y->type == 1) {
                return same_tree(m, x->a, y->a);
        }

        if (x->type == 2 && y->type == 2) {
                if (x->b - x->a != y->b - y->a) {
                        return false;
                }
                for (i64 k = 0; k < x->b - x->a; ++k) {
                        if (!same_tree(m, kid(s, x->c, x->a + k), kid(s, y->c, y->a + k))) {
                                return false;
                        }
                }
                return true;
        }

        if (x->type == 3 && y->type == 3) {
                return at(s->text, x->a) == at(s->text, y->a);
        }

        if (x->type == 4 || y->type == 4) {
                return (x->type == 4)
                    && (y->type == 4)
                    && (x->b - x->a == y->b - y->a)
                    && (memcmp(m->src + x->a, m->src + y->a, x->b - x->a) == 0);
        }

        SynBind const *t = (x->type == 3) ? x : y;
        SynBind const *n = (x->type == 3) ? y : x;

        return (n->type == 1)
            && (at(s->ftok, n->a) == at(s->ltok, n->a))
            && (at(s->ftok, n->a) >= 0)
            && (at(s->text, at(s->ftok, n->a)) == at(s->text, t->a));
}

static i64
global_slot(SynMatch const *m, i64 slot)
{
        if (slot < 0 || m->p->slotmap == NULL || slot >= len(m->p->slotmap)) {
                return slot;
        }

        return at(m->p->slotmap, slot);
}

static bool
mbind(SynMatch *m, i64 slot, SynBind b)
{
        slot = global_slot(m, slot);

        if (slot < 0) {
                return true;
        }

        SynBind *old = v_(m->binds, slot);

        if (old->type != 0) {
                return same_bind(m, old, &b);
        }

        *old = b;
        xvP(m->trail, slot);

        return true;
}

static void
map_edge(SynMatch *m, I64Vec *map, i64 tag, i64 p, i64 s)
{
        if (p < 0 || s < 0 || v__(*map, p) >= 0) {
                return;
        }

        v__(*map, p) = s;
        xvP(m->tails, 2 * p + tag);
}

static void
map_first(SynMatch *m, i64 p, i64 s)
{
        map_edge(m, &m->tokmap, 0, p, s);
}

static void
map_last(SynMatch *m, i64 p, i64 s)
{
        map_edge(m, &m->lastmap, 1, p, s);
}

static void
map_token(SynMatch *m, i64 p, i64 s)
{
        map_first(m, p, s);
        map_last(m, p, s);
}

typedef struct {
        usize trail;
        usize tails;
} SynMark;

static SynMark
mark(SynMatch const *m)
{
        return (SynMark) { vN(m->trail), vN(m->tails) };
}

static void
undo(SynMatch *m, SynMark k)
{
        while (vN(m->trail) > k.trail) {
                v_(m->binds, vXx(m->trail))->type = 0;
        }

        while (vN(m->tails) > k.tails) {
                i64 t = vXx(m->tails);
                if (t % 2 == 0) {
                        v__(m->tokmap, t / 2) = -1;
                } else {
                        v__(m->lastmap, t / 2) = -1;
                }
        }
}

static bool
kind_ok(SynMatch const *m, i64 p, i64 s)
{
        Value const *ks = v_(*m->p->kinds, p);

        if (ks->type != VALUE_ARRAY || vN(*ks->array) == 0) {
                return true;
        }

        i64 inner = unparen(m, &m->s, s);

        for (usize i = 0; i < vN(*ks->array); ++i) {
                i64 k = at(ks->array, i);
                if (
                        (k == at(m->s.kind, s))
                     || (k == at(m->s.kind, inner))
                     || (k == at(m->s.form, s))
                ) {
                        return true;
                }
        }

        return false;
}

static bool
has_dynamic(T2Universe const *u, T2Type t, int depth)
{
        if (depth > 64) {
                return false;
        }

        switch (t2_type_kind(u, t)) {
        case T2_TYPE_DYNAMIC:
        case T2_TYPE_UNKNOWN:
        case T2_TYPE_ERROR:
                return true;

        default:
                break;
        }

        for (usize i = 0; i < t2_type_arity(u, t); ++i) {
                if (has_dynamic(u, t2_type_child(u, t, i), depth + 1)) {
                        return true;
                }
        }

        return false;
}

static bool
unknown_type(T2Universe const *u, i64 t)
{
        if (t <= 0) {
                return true;
        }

        switch (t2_type_kind(u, (T2Type)t)) {
        case T2_TYPE_DYNAMIC:
        case T2_TYPE_UNKNOWN:
        case T2_TYPE_ERROR:
        case T2_TYPE_VARIABLE:
        case T2_TYPE_META:
        case T2_TYPE_PARAMETER:
                return true;

        default:
                return false;
        }
}

static bool
type_ok(SynMatch const *m, i64 p, i64 s)
{
        i64 want = opt(m->p->tyhole, p);

        if (want == -1) {
                return true;
        }

        bool gradual = (opt(m->p->tymode, p) == TYPE_HOLE_GRADUAL);
        i64 have = opt(m->s.ty, unparen(m, &m->s, s));
        T2Universe const *u = t2_global_universe();

        if (unknown_type(u, have)) {
                return gradual;
        }

        if (want <= 0) {
                return false;
        }

        if (t2_gradual_subtype(u, (T2Type)have, (T2Type)want) != T2_RELATION_YES) {
                return false;
        }

        return gradual || !has_dynamic(u, (T2Type)have, 0);
}

static bool
same_layout(SynMatch const *m, i64 p, i64 s)
{
        Packed const *P = m->p;
        Packed const *S = &m->s;

        i64 pf = at(P->ftok, p);
        i64 pl = at(P->ltok, p);
        i64 sf = at(S->ftok, s);
        i64 sl = at(S->ltok, s);

        if (pf < 0 || sf < 0 || pl - pf != sl - sf) {
                return true;
        }

        for (i64 k = 1; k <= pl - pf; ++k) {
                i64 pn = at(P->tnum, pf + k - 1) + at(P->lnum, pf + k);
                i64 sn = at(S->tnum, sf + k - 1) + at(S->lnum, sf + k);
                i64 pnl = at(P->tnl, pf + k - 1) + at(P->lnl, pf + k);
                i64 snl = at(S->tnl, sf + k - 1) + at(S->lnl, sf + k);
                if ((pn == 0) != (sn == 0) || pnl != snl) {
                        return false;
                }
        }

        return true;
}

static bool
regex_ok(SynMatch const *m, Value const *re, char const *s, i64 n)
{
        Ty *ty = m->ty;

        if (re->type != VALUE_REGEX) {
                return true;
        }

        return pcre2_match(
                re->regex->pcre2,
                (PCRE2_SPTR)s,
                n,
                0,
                0,
                ty->pcre2.match,
                ty->pcre2.ctx
        ) > 0;
}

static bool
comment_body(char const *s, i64 n, i64 *a, i64 *b)
{
        for (i64 i = 0; i + 1 < n; ++i) {
                if (s[i] == '/' && s[i + 1] == '*') {
                        i64 depth = 0;
                        for (; i + 1 < n; ++i) {
                                if (s[i] == '/' && s[i + 1] == '*') {
                                        depth += 1;
                                        i += 1;
                                } else if (s[i] == '*' && s[i + 1] == '/') {
                                        depth -= 1;
                                        i += 1;
                                        if (depth == 0) {
                                                break;
                                        }
                                }
                        }
                        continue;
                }
                if (s[i] != '/' || s[i + 1] != '/') {
                        continue;
                }
                i64 j = i + 2;
                if (j < n && s[j] == '/') {
                        j += 1;
                }
                if (j < n && (s[j] == ' ' || s[j] == '\t')) {
                        j += 1;
                }
                i64 k = j;
                while (k < n && s[k] != '\n') {
                        k += 1;
                }
                while (j < k && (s[j] == ' ' || s[j] == '\t')) {
                        j += 1;
                }
                while (k > j && (s[k - 1] == ' ' || s[k - 1] == '\t' || s[k - 1] == '\r')) {
                        k -= 1;
                }
                *a = j;
                *b = k;
                return true;
        }

        return false;
}

static bool
gap_ok(SynMatch *m, Value const *g)
{
        Packed const *S = &m->s;

        i64 before = at(g->array, 0);
        i64 after  = at(g->array, 1);
        i64 code   = at(g->array, 2);
        i64 slot   = at(g->array, 3);
        Value const *extra = v_(*g->array, 4);

        if (code == GAP_ANY) {
                return true;
        }

        i64 b = (before < 0) ? -1 : v__(m->lastmap, before);
        i64 a = (after < 0) ? -1 : v__(m->tokmap, after);

        if ((before >= 0 && b < 0) || (after >= 0 && a < 0) || (a < 0 && b < 0)) {
                return false;
        }

        bool spans = (a >= 0 && b >= 0 && b + 1 != a);

        if (spans && code != GAP_REGEX && code != GAP_BIND) {
                return false;
        }

        if (spans && a < b) {
                return false;
        }

        i64 num = ((b >= 0) ? at(S->tnum, b) : 0) + ((a >= 0) ? at(S->lnum, a) : 0);
        i64 nl  = ((b >= 0) ? at(S->tnl,  b) : 0) + ((a >= 0) ? at(S->lnl,  a) : 0);
        i64 cm  = ((b >= 0) ? at(S->tcm,  b) : 0) + ((a >= 0) ? at(S->lcm,  a) : 0);
        i64 sp  = ((b >= 0) ? at(S->tspc, b) : 0) + ((a >= 0) ? at(S->lspc, a) : 0);

        i64 lo = (b >= 0) ? at(S->tend, b) : at(S->tstart, a) - at(S->llen, a);
        i64 hi = (a >= 0) ? at(S->tstart, a) : at(S->tend, b) + at(S->tlen, b);
        char const *text = m->src + lo;
        i64 n = hi - lo;
        i64 ca;
        i64 cb;

        switch (code) {
        case GAP_NONE:
                return num == 0;

        case GAP_SPACE:
                return num > 0 && sp == num;

        case GAP_NEWLINE:
                return nl == 1 && cm == 0;

        case GAP_BLANK:
                return nl >= 2;

        case GAP_BIND:
                return mbind(m, slot, (SynBind) { 4, lo, hi, 0 });

        case GAP_REGEX:
                return regex_ok(m, extra, text, n)
                    && mbind(m, slot, (SynBind) { 4, lo, hi, 0 });

        case GAP_COMMENT:
                return comment_body(text, n, &ca, &cb);

        case GAP_COMMENT_BIND:
                return comment_body(text, n, &ca, &cb)
                    && mbind(m, slot, (SynBind) { 4, lo + ca, lo + cb, 0 });

        case GAP_COMMENT_REGEX:
                return comment_body(text, n, &ca, &cb)
                    && regex_ok(m, extra, text + ca, cb - ca);

        case GAP_COMMENT_TEXT:
                return comment_body(text, n, &ca, &cb)
                    && (extra->type == VALUE_STRING)
                    && ((i64)sN(*extra) == cb - ca)
                    && (memcmp(ss(*extra), text + ca, cb - ca) == 0);

        default:
                return true;
        }
}

static bool
gaps_ok(SynMatch *m)
{
        Array const *gaps = m->p->gaps;

        for (i64 i = 0; i < len(gaps); ++i) {
                Value const *g = v_(*gaps, i);
                if (g->type != VALUE_ARRAY || vN(*g->array) != 5) {
                        continue;
                }
                if (!gap_ok(m, g)) {
                        return false;
                }
        }

        return true;
}

static bool
match_seq(SynMatch *m, i64 pp, i64 i, i64 sp, i64 j, bool prefix);

static bool
match_root(SynMatch *m, i64 sub, i64 s);

static bool
match_hole(SynMatch *m, i64 p, i64 s)
{
        Packed const *P = m->p;

        if (!kind_ok(m, p, s) || !type_ok(m, p, s)) {
                return false;
        }

        i64 deep = (P->deep == NULL) ? -1 : at(P->deep, p);

        if (deep >= 0) {
                vec(i64) stack = {0};
                bool found = false;

                xvP(stack, s);

                while (!found && vN(stack) > 0) {
                        i64 n = vXx(stack);
                        SynMark mk = mark(m);
                        if (match_root(m, deep, n)) {
                                found = true;
                                break;
                        }
                        undo(m, mk);
                        for (i64 k = nkids(&m->s, n) - 1; k >= 0; --k) {
                                xvP(stack, kid(&m->s, n, k));
                        }
                }

                xvF(stack);

                if (!found) {
                        return false;
                }
        }

        Value const *alts = (P->alts == NULL) ? NULL : v_(*P->alts, p);

        if (alts != NULL && alts->type == VALUE_ARRAY && vN(*alts->array) > 0) {
                bool found = false;
                for (usize k = 0; !found && k < vN(*alts->array); ++k) {
                        SynMark mk = mark(m);
                        if (match_root(m, at(alts->array, k), s)) {
                                found = true;
                        } else {
                                undo(m, mk);
                        }
                }
                if (!found) {
                        return false;
                }
        }

        return mbind(m, at(P->hole, p), (SynBind) { 1, s, 0, 0 });
}

static bool
match_node(SynMatch *m, i64 p, i64 s)
{
        Packed const *P = m->p;
        Packed const *S = &m->s;

        if (at(P->hole, p) != -1) {
                if (!match_hole(m, p, s)) {
                        return false;
                }
                map_first(m, at(P->ftok, p), at(S->ftok, s));
                map_last(m, at(P->ltok, p), at(S->ltok, s));
                return true;
        }

        if (at(P->kind, p) == m->paren && at(S->kind, s) != m->paren && nkids(P, p) == 1) {
                return match_node(m, kid(P, p, 0), s);
        }

        if (at(S->kind, s) == m->paren && at(P->kind, p) != m->paren && nkids(S, s) == 1) {
                return match_node(m, p, kid(S, s, 0));
        }

        bool sem = (opt(S->sem, 0) == 1);

        if (opt(P->ref, p) >= 0 && (sem || opt(S->ref, s) >= 0)) {
                if (opt(P->ref, p) != opt(S->ref, s)) {
                        return false;
                }
                map_first(m, at(P->ftok, p), at(S->ftok, s));
                map_last(m, at(P->ltok, p), at(S->ltok, s));
                return true;
        }

        if (opt(P->callee, p) >= 0 && (sem || opt(S->callee, s) >= 0)) {
                if (
                        (opt(P->callee, p) != opt(S->callee, s))
                     || (nkids(P, p) == 0)
                     || (nkids(S, s) == 0)
                     || !match_seq(m, p, 1, s, 1, false)
                ) {
                        return false;
                }
                map_first(m, at(P->ftok, p), at(S->ftok, s));
                map_last(m, at(P->ltok, p), at(S->ltok, s));
                return true;
        }

        if (at(P->kind, p) != at(S->kind, s) || at(P->form, p) != at(S->form, s)) {
                return false;
        }

        i64 i = at(P->ostart, p);
        i64 j = at(S->ostart, s);
        i64 ie = i + at(P->ocount, p);
        i64 je = j + at(S->ocount, s);

        for (;;) {
                while (i < ie && at(P->punct, at(P->own, i))) {
                        i += 1;
                }
                while (j < je && at(S->punct, at(S->own, j))) {
                        j += 1;
                }
                if (i == ie || j == je) {
                        break;
                }
                i64 pt = at(P->own, i);
                i64 st = at(S->own, j);
                i64 th = at(P->tokhole, pt);
                if (th != -1) {
                        if (!mbind(m, th, (SynBind) { 3, st, 0, 0 })) {
                                return false;
                        }
                } else if (at(P->text, pt) != at(S->text, st)) {
                        return false;
                }
                map_token(m, pt, st);
                i += 1;
                j += 1;
        }

        if (i != ie || j != je) {
                return false;
        }

        if (at(P->ocount, p) == at(S->ocount, s)) {
                for (i64 k = 0; k < at(P->ocount, p); ++k) {
                        map_token(
                                m,
                                at(P->own, at(P->ostart, p) + k),
                                at(S->own, at(S->ostart, s) + k)
                        );
                }
        }

        if (!match_seq(m, p, 0, s, 0, false)) {
                return false;
        }

        if (len(P->mode) > 0 && at(P->mode, 0) == 1 && !same_layout(m, p, s)) {
                return false;
        }

        map_first(m, at(P->ftok, p), at(S->ftok, s));
        map_last(m, at(P->ltok, p), at(S->ltok, s));

        return true;
}

static bool
match_seq(SynMatch *m, i64 pp, i64 i, i64 sp, i64 j, bool prefix)
{
        Packed const *P = m->p;
        Packed const *S = &m->s;

        i64 np = nkids(P, pp);
        i64 ns = nkids(S, sp);

        if (i == np) {
                return prefix || j == ns;
        }

        i64 p = kid(P, pp, i);
        i64 slot = at(P->seq, p);

        if (slot != -1) {
                for (i64 k = j; k <= ns; ++k) {
                        SynMark mk = mark(m);
                        if (
                                mbind(m, slot, (SynBind) { 2, j, k, sp })
                             && match_seq(m, pp, i + 1, sp, k, prefix)
                        ) {
                                return true;
                        }
                        undo(m, mk);
                }
                return false;
        }

        if (j >= ns) {
                return false;
        }

        SynMark mk = mark(m);

        if (match_node(m, p, kid(S, sp, j)) && match_seq(m, pp, i + 1, sp, j + 1, prefix)) {
                return true;
        }

        undo(m, mk);

        return false;
}

static bool
match_in(SynMatch *m, i64 s)
{
        Packed const *P = m->p;

        if (len(P->roots) == 1) {
                return match_node(m, at(P->roots, 0), s) && gaps_ok(m);
        }

        for (i64 j = 0; j <= nkids(&m->s, s); ++j) {
                SynMark mk = mark(m);
                if (match_seq(m, 0, 0, s, j, true) && gaps_ok(m)) {
                        return true;
                }
                undo(m, mk);
        }

        return false;
}

static bool
match_root(SynMatch *m, i64 sub, i64 s)
{
        if (sub < 0 || sub >= (i64)vN(m->subs)) {
                return false;
        }

        Packed const *outer = m->p;
        I64Vec tokmap = m->tokmap;
        I64Vec lastmap = m->lastmap;
        I64Vec tails = m->tails;

        m->p = v_(m->subs, sub);
        m->tokmap = (I64Vec) {0};
        m->lastmap = (I64Vec) {0};
        m->tails = (I64Vec) {0};

        for (i64 i = 0; i < len(m->p->text); ++i) {
                xvP(m->tokmap, -1);
                xvP(m->lastmap, -1);
        }

        usize trail = vN(m->trail);
        bool ok = match_in(m, s);

        xvF(m->tokmap);
        xvF(m->lastmap);
        xvF(m->tails);

        m->p = outer;
        m->tokmap = tokmap;
        m->lastmap = lastmap;
        m->tails = tails;

        if (!ok) {
                while (vN(m->trail) > trail) {
                        v_(m->binds, vXx(m->trail))->type = 0;
                }
        }

        return ok;
}

// ty/syntax.unify(
//     pattern: _,
//     subs: _,
//     subject: _,
//     source: String,
//     target: Int,
//     start: Int,
//     slots: Int,
//     paren: Int
// ) -> _
TY_BUILTIN_RAW(ty_syntax_unify)
{
        ASSERT_ARGC("ty.syntax.unify()", 8);

        SynMatch m = { .ty = ty };
        Packed main;

        unpack(&ARG(0), &main);
        unpack(&ARG(2), &m.s);

        Value subs   = ARGx(1, VALUE_ARRAY);
        Value source = ARGx(3, VALUE_STRING);
        i64 target   = ARGx(4, VALUE_INTEGER).z;
        i64 start    = ARGx(5, VALUE_INTEGER).z;
        i64 slots    = ARGx(6, VALUE_INTEGER).z;
        m.paren      = ARGx(7, VALUE_INTEGER).z;
        m.p          = &main;
        m.src        = (char const *)ss(source);

        if (
                (main.kind == NULL) || (main.hole == NULL) || (main.kinds == NULL)
             || (main.roots == NULL) || (m.s.kind == NULL) || (m.s.text == NULL)
             || (m.s.lnum == NULL) || (main.lnum == NULL)
             || (m.s.tstart == NULL) || (m.s.llen == NULL)
        ) {
                zP("ty.syntax.unify(): malformed packed tree");
        }

        for (usize i = 0; i < vN(*subs.array); ++i) {
                Packed sub;
                unpack(v_(*subs.array, i), &sub);
                xvP(m.subs, sub);
        }

        for (i64 i = 0; i < slots; ++i) {
                xvP(m.binds, ((SynBind) { 0 }));
        }

        for (i64 i = 0; i < len(main.text); ++i) {
                xvP(m.tokmap, -1);
                xvP(m.lastmap, -1);
        }

        bool ok = false;
        i64 pos = -1;

        if (len(main.roots) == 1) {
                ok = match_node(&m, at(main.roots, 0), target) && gaps_ok(&m);
        } else {
                for (i64 j = start; !ok && j <= nkids(&m.s, target); ++j) {
                        SynMark mk = mark(&m);
                        if (match_seq(&m, 0, 0, target, j, true) && gaps_ok(&m)) {
                                ok = true;
                                pos = j;
                        } else {
                                undo(&m, mk);
                        }
                }
        }

        Value result = NIL;

        if (ok) {
                Array *binds = vA();
                Array *tokmap = vA();
                Array *lastmap = vA();

                gP(&ARRAY(binds));
                gP(&ARRAY(tokmap));
                gP(&ARRAY(lastmap));

                for (i64 i = 0; i < slots; ++i) {
                        SynBind const *b = v_(m.binds, i);
                        vAp(binds, (b->type == 0) ? NIL : vT(4));
                        if (b->type != 0) {
                                Value *t = vvL(*binds);
                                t->items[0] = INTEGER(b->type);
                                t->items[1] = INTEGER(b->a);
                                t->items[2] = INTEGER(b->b);
                                t->items[3] = INTEGER(b->c);
                        }
                }

                for (usize i = 0; i < vN(m.tokmap); ++i) {
                        vAp(tokmap, INTEGER(v__(m.tokmap, i)));
                        vAp(lastmap, INTEGER(v__(m.lastmap, i)));
                }

                result = vT(4);
                result.items[0] = ARRAY(binds);
                result.items[1] = ARRAY(tokmap);
                result.items[2] = INTEGER(pos);
                result.items[3] = ARRAY(lastmap);

                gX();
                gX();
                gX();
        }

        xvF(m.subs);
        xvF(m.binds);
        xvF(m.trail);
        xvF(m.tokmap);
        xvF(m.lastmap);
        xvF(m.tails);

        return result;
}

// ty/syntax.members(mod: Module) -> Array[Array[{kind: String, start: Int, end: Int}]]
TY_BUILTIN_RAW(ty_syntax_members)
{
        ASSERT_ARGC("ty.syntax.members()", 1);

        Module *mod = ARGx(0, VALUE_MODULE).mod;
        Array *out = vA();

        gP(&ARRAY(out));

        for (int i = 0; mod->prog != NULL && mod->prog[i] != NULL; ++i) {
                Stmt const *s = mod->prog[i];
                if (s->type != STATEMENT_CLASS_DEFINITION) {
                        continue;
                }
                Array *members = vA();
                vAp(out, ARRAY(members));
                for (usize j = 0; j < vN(sF(s, class).members); ++j) {
                        Expr const *m = v__(sF(s, class).members, j);
                        vAp(members, vTn(
                                "kind",  xSz(kind_name(m)),
                                "start", INTEGER(m->start.byte),
                                "end",   INTEGER(m->end.byte)
                        ));
                }
        }

        gX();

        return ARRAY(out);
}

// ty/syntax.mark(kind: String, start: Int, end: Int) -> Bool
TY_BUILTIN_RAW(ty_syntax_mark)
{
        ASSERT_ARGC("ty.syntax.mark()", 3);

        Value kind = ARGx(0, VALUE_STRING);
        i64 start  = ARGx(1, VALUE_INTEGER).z;
        i64 end    = ARGx(2, VALUE_INTEGER).z;

        if (start < 0 || end < start) {
                return BOOLEAN(false);
        }

        return BOOLEAN(parse_mark_region(ty, TY_TMP_C_STR(kind), start, end));
}

static Module *
scope_module(Ty *ty, Value const *v)
{
        if (v->type == VALUE_MODULE) {
                return v->mod;
        }

        if (v->type != VALUE_STRING) {
                return NULL;
        }

        char const *name = TY_TMP_C_STR(*v);
        ModuleVector const *mods = TyActiveModules(ty);

        for (usize i = 0; i < vN(*mods); ++i) {
                Module *mod = v__(*mods, i);
                if (mod->path != NULL && strcmp(mod->path, name) == 0) {
                        return mod;
                }
        }

        for (usize i = 0; i < vN(*mods); ++i) {
                Module *mod = v__(*mods, i);
                if (mod->name != NULL && strcmp(mod->name, name) == 0) {
                        return mod;
                }
        }

        return NULL;
}

static char const *
symbol_kind(Symbol const *sym)
{
        if (SymbolIsMacro(sym) || SymbolIsFunMacro(sym)) {
                return "macro";
        }
        if (SymbolIsClass(sym)) {
                return "class";
        }
        if (SymbolIsTag(sym)) {
                return "tag";
        }
        if (SymbolIsTypeVar(sym)) {
                return "type-var";
        }
        if (SymbolIsTypeAlias(sym) || SymbolIsTypeFunction(sym)) {
                return "type";
        }
        if (SymbolIsNamespace(sym)) {
                return "namespace";
        }
        if (SymbolIsMember(sym)) {
                return "member";
        }
        if (SymbolIsFunction(sym)) {
                return "function";
        }

        return "variable";
}

static i64
symbol_id(Symbol const *sym)
{
        return (sym == NULL || sym->identifier == NULL) ? -1 : (i64)sym->symbol;
}

static Value
symbol_record(Ty *ty, Symbol const *sym, Module const *home)
{
        Module const *mod = sym->mod;

        return vTn(
                "id",       INTEGER(sym->symbol),
                "name",     xSz(sym->identifier),
                "kind",     xSz(symbol_kind(sym)),
                "module",   (mod == NULL || mod->name == NULL) ? NIL : xSz(mod->name),
                "path",     (mod == NULL || mod->path == NULL) ? NIL : xSz(mod->path),
                "line",     INTEGER(LocLine(sym->loc) + 1),
                "col",      INTEGER(LocCol(sym->loc) + 1),
                "byte",     INTEGER(sym->loc.byte),
                "here",     BOOLEAN(home != NULL && mod == home),
                "global",   BOOLEAN(SymbolIsGlobal(sym)),
                "public",   BOOLEAN(SymbolIsPublic(sym)),
                "builtin",  BOOLEAN(SymbolIsBuiltin(sym)),
                "captured", BOOLEAN(SymbolIsCaptured(sym)),
                "const",    BOOLEAN(SymbolIsConst(sym)),
                "type",     INTEGER((sym->type == T2_TYPE_INVALID) ? -1 : (i64)sym->type),
                "doc",      (sym->doc == NULL) ? NIL : xSz(sym->doc)
        );
}

static Symbol *
expr_symbol(Expr const *e)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_PACK:
                return xF(e, symbol);

        default:
                return NULL;
        }
}

static Symbol *
callee_symbol(Expr const *e)
{
        if (
                (e->type != EXPRESSION_FUNCTION_CALL)
             || (xF(e, function) == NULL)
             || (xF(e, function)->type != EXPRESSION_IDENTIFIER)
        ) {
                return NULL;
        }

        return xF(xF(e, function), symbol);
}

static Symbol *
stmt_symbol(Stmt const *s)
{
        switch (s->type) {
        case STATEMENT_CLASS_DEFINITION: return sF(s, class).var;
        case STATEMENT_TAG_DEFINITION:   return sF(s, tag).var;
        default:                         return NULL;
        }
}

static T2Type
node_type(SyntaxNode const *node)
{
        if (node->e == NULL || node->kind > STATEMENT_TYPE_START) {
                return T2_TYPE_INVALID;
        }

        return ((Expr const *)node->e)->_type;
}

static char const *
param_name(char const *src, u32 start, u32 end, usize *n)
{
        char const *p = src + start;
        char const *q = src + end;

        while (p < q && (*p == '*' || *p == '%' || *p == '&' || *p == ' ')) {
                p += 1;
        }

        char const *r = p;

        while (
                (r < q)
             && (*r != ':')
             && (*r != '=')
             && (*r != ' ')
             && (*r != ',')
             && (*r != ')')
        ) {
                r += 1;
        }

        *n = r - p;

        return p;
}

static Symbol *
param_symbol(Module const *mod, SyntaxNode const *param, Expr const *fn)
{
        usize n;
        char const *name = param_name(mod->source, param->start, param->end, &n);

        for (usize i = 0; i < vN(xF(fn, param_symbols)); ++i) {
                Symbol *sym = v__(xF(fn, param_symbols), i);
                if (
                        (sym != NULL)
                     && (sym->identifier != NULL)
                     && (strlen(sym->identifier) == n)
                     && (memcmp(sym->identifier, name, n) == 0)
                ) {
                        return sym;
                }
        }

        return NULL;
}

static bool
defines(Symbol const *sym, Module const *mod, u32 start)
{
        return (sym->mod == mod) && (sym->loc.byte == start);
}

typedef struct {
        Ty *ty;
        char const *src;
        usize n;
        vec(Expr *) all;
        PtrSet seen;
} Resolved;

static Expr *
collect_e(Expr *e, Scope *scope, void *u)
{
        Resolved *r = u;

        if (
                (e == NULL)
             || pset_has(&r->seen, e)
             || (LocS(e->start) < r->src)
             || (LocS(e->start) > r->src + r->n)
             || (e->start.byte >= e->end.byte)
             || (e->end.byte > r->n)
        ) {
                return e;
        }

        pset_add(r->ty, &r->seen, e);
        xvP(r->all, e);

        return e;
}

static Expr *
collect_l(Expr *e, bool def, Scope *scope, void *u)
{
        return collect_e(e, scope, u);
}

static int
by_span(void const *a, void const *b)
{
        Expr const *x = *(Expr const **)a;
        Expr const *y = *(Expr const **)b;

        if (x->start.byte != y->start.byte) {
                return (x->start.byte < y->start.byte) ? -1 : 1;
        }

        if (x->end.byte != y->end.byte) {
                return (x->end.byte < y->end.byte) ? -1 : 1;
        }

        return 0;
}

static void
collect_resolved(Ty *ty, Module *mod, Resolved *r)
{
        VisitorCtx visitor = visit_identity(ty);
        visitor.e_pre = collect_e;
        visitor.t_pre = collect_e;
        visitor.p_pre = collect_e;
        visitor.l_pre = collect_l;
        visitor.user  = r;

        r->ty = ty;
        r->src = mod->source;
        r->n = strlen(mod->source);

        for (int i = 0; mod->prog != NULL && mod->prog[i] != NULL; ++i) {
                visit_statement(ty, mod->prog[i], NULL, &visitor);
        }

        qsort(vv(r->all), vN(r->all), sizeof (Expr *), by_span);
}

static Expr const *
resolved_twin(Resolved const *r, SyntaxNode const *node, bool want_symbol)
{
        isize lo = 0;
        isize hi = vN(r->all);

        while (lo < hi) {
                isize mid = (lo + hi) / 2;
                Expr const *x = v__(r->all, mid);
                if (
                        (x->start.byte < node->start)
                     || (x->start.byte == node->start && x->end.byte < node->end)
                ) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        for (isize i = lo; i < vN(r->all); ++i) {
                Expr const *x = v__(r->all, i);
                if (x->start.byte != node->start || x->end.byte != node->end) {
                        break;
                }
                if (x == node->e) {
                        continue;
                }
                if (want_symbol && expr_symbol(x) != NULL) {
                        return x;
                }
                if (!want_symbol && x->type == node->kind && x->_type != T2_TYPE_INVALID) {
                        return x;
                }
        }

        return NULL;
}

typedef struct {
        vec(i64) ref;
        vec(i64) callee;
        vec(i64) type;
        vec(bool) def;
} SemInfo;

typedef vec(Symbol const *) SymVec;

static void
collect_semantics(Ty *ty, Module *mod, SemInfo *info, SymVec *symbols)
{
        PtrSet seen = {0};
        Resolved resolved = {0};

        collect_resolved(ty, mod, &resolved);

        for (isize i = 0; i < vN(mod->syntax); ++i) {
                SyntaxNode const *node = v_(mod->syntax, i);
                Symbol *ref = NULL;
                Symbol *callee = NULL;
                bool def = false;

                if (node->e != NULL && node->kind > STATEMENT_TYPE_START) {
                        ref = stmt_symbol(node->e);
                        def = (ref != NULL);
                } else if (node->e != NULL) {
                        ref = expr_symbol(node->e);
                        callee = callee_symbol(node->e);
                        def = (ref != NULL) && defines(ref, mod, node->start);
                } else if (node->kind == SYNTAX_PARAM && node->parent >= 0) {
                        SyntaxNode const *fn = v_(mod->syntax, node->parent);
                        if (
                                (fn->e != NULL)
                             && (fn->kind < STATEMENT_TYPE_START)
                             && (((Expr const *)fn->e)->type == EXPRESSION_FUNCTION)
                        ) {
                                ref = param_symbol(mod, node, fn->e);
                                def = (ref != NULL);
                        }
                }

                T2Type t = node_type(node);

                bool expr = (node->e != NULL) && (node->kind < STATEMENT_TYPE_START);

                if (expr && ref == NULL && node->kind == EXPRESSION_IDENTIFIER) {
                        Expr const *twin = resolved_twin(&resolved, node, true);
                        if (twin != NULL) {
                                ref = expr_symbol(twin);
                                def = defines(ref, mod, node->start);
                        }
                }

                if (expr && t == T2_TYPE_INVALID) {
                        Expr const *twin = resolved_twin(&resolved, node, false);
                        if (twin != NULL) {
                                t = twin->_type;
                        }
                }

                xvP(info->ref,    symbol_id(ref));
                xvP(info->callee, symbol_id(callee));
                xvP(info->type,   (t == T2_TYPE_INVALID) ? -1 : (i64)t);
                xvP(info->def,    def);

                Symbol const *both[] = { ref, callee };

                for (usize k = 0; k < countof(both); ++k) {
                        Symbol const *sym = both[k];
                        if (symbol_id(sym) < 0) {
                                continue;
                        }
                        void *key = (void *)(((uptr)sym->symbol + 1) << 4);
                        if (!pset_has(&seen, key)) {
                                pset_add(ty, &seen, key);
                                xvP(*symbols, sym);
                        }
                }
        }

        xvF(resolved.all);
}

static void
free_semantics(SemInfo *info)
{
        xvF(info->ref);
        xvF(info->callee);
        xvF(info->type);
        xvF(info->def);
}

// ty/syntax.semantics(mod: Module) -> {
//     ref: Array[Int],
//     callee: Array[Int],
//     type: Array[Int],
//     def: Array[Bool],
//     symbols: Array[_]
// }
TY_BUILTIN_RAW(ty_syntax_semantics)
{
        ASSERT_ARGC("ty.syntax.semantics()", 1);

        Module *mod = ARGx(0, VALUE_MODULE).mod;

        if (!mod->has_syntax) {
                syntax_snapshot(ty, mod);
        }

        Array *refs    = vA();
        Array *callees = vA();
        Array *types   = vA();
        Array *defs    = vA();
        Array *symbols = vA();

        GC_STOP();
        SCRATCH_SAVE();

        SemInfo info = {0};
        SymVec syms = {0};
        collect_semantics(ty, mod, &info, &syms);

        for (usize i = 0; i < vN(syms); ++i) {
                vAp(symbols, symbol_record(ty, v__(syms, i), mod));
        }

        xvF(syms);

        for (usize i = 0; i < vN(info.ref); ++i) {
                vAp(refs,    INTEGER(v__(info.ref, i)));
                vAp(callees, INTEGER(v__(info.callee, i)));
                vAp(types,   INTEGER(v__(info.type, i)));
                vAp(defs,    BOOLEAN(v__(info.def, i)));
        }

        free_semantics(&info);

        SCRATCH_RESTORE();

        Value result = vTn(
                "ref",     ARRAY(refs),
                "callee",  ARRAY(callees),
                "type",    ARRAY(types),
                "def",     ARRAY(defs),
                "symbols", ARRAY(symbols)
        );

        GC_RESUME();

        return result;
}

enum {
        TRIVIA_NEWLINE,
        TRIVIA_SPACE,
        TRIVIA_DOC,
        TRIVIA_COMMENT,
        TRIVIA_BLOCK,
        TRIVIA_DIRECTIVE,
        TRIVIA_SHEBANG,
        TRIVIA_BOM,
        TRIVIA_RAW
};

static char const *TriviaKinds[] = {
        "newline",
        "space",
        "doc",
        "comment",
        "block",
        "directive",
        "shebang",
        "bom",
        "raw"
};

enum {
        NODE_TREE,
        NODE_KIND,
        NODE_FORM,
        NODE_START,
        NODE_END,
        NODE_INDEX,
        NODE_PARENT,
        NODE_NODES,
        NODE_CORE,
        NODE_SYNTH,
        NODE_OWN,
        NODE_FTOK,
        NODE_LTOK,
        NODE_SYM,
        NODE_CALLEE,
        NODE_TYPE,
        NODE_DEF,
        NODE_SLOTS
};

static char const *NodeFields[] = {
        "tree", "kind", "form", "start", "end", "index", "parent", "nodes", "core",
        "synth", "own", "ftok", "ltok", "symId", "calleeId", "typeId", "def?"
};

enum {
        TOKEN_KIND,
        TOKEN_START,
        TOKEN_END_,
        TOKEN_TEXT,
        TOKEN_INDEX,
        TOKEN_OWNER,
        TOKEN_LEADING,
        TOKEN_TRAILING,
        TOKEN_SLOTS
};

static char const *TokenFields[] = {
        "kind", "start", "end", "text", "index", "owner", "leading", "trailing"
};

enum {
        TRIVIA_KIND,
        TRIVIA_START,
        TRIVIA_END,
        TRIVIA_TEXT,
        TRIVIA_SLOTS
};

static char const *TriviaFields[] = { "kind", "start", "end", "text" };

enum {
        TREE_ROOT,
        TREE_NODES,
        TREE_EVERY,
        TREE_TOKENS,
        TREE_EOF,
        TREE_LINES,
        TREE_SLOTS
};

enum {
        SF_ID,
        SF_NAME,
        SF_KIND,
        SF_MODULE,
        SF_PATH,
        SF_LINE,
        SF_COL,
        SF_BYTE,
        SF_HERE,
        SF_GLOBAL,
        SF_PUBLIC,
        SF_BUILTIN,
        SF_CAPTURED,
        SF_CONST,
        SF_TYPE,
        SF_DOC,
        SF_SLOTS
};

static char const *SymbolFields[] = {
        "id", "name", "kind", "module", "path", "line", "col", "byte", "here?", "global?",
        "public?", "builtin?", "captured?", "const?", "typeId", "doc"
};

static char const *TreeFields[] = { "root", "nodes", "every", "tokens", "eof", "lineStarts" };

typedef struct {
        int class;
        u16 slots[NODE_SLOTS > SF_SLOTS ? NODE_SLOTS : SF_SLOTS];
} SynLayout;

static pthread_mutex_t SynLock = PTHREAD_MUTEX_INITIALIZER;
static InternSet SynInterned;
static vec(SynLayout *) SynLayouts;
static char *SynKindNames[STATEMENT_TYPE_START + countof(StmtKinds) + 12];

static u16 const *
syn_layout(Ty *ty, int class, char const **names, usize n)
{
        for (usize i = 0; i < vN(SynLayouts); ++i) {
                if (v__(SynLayouts, i)->class == class) {
                        return v__(SynLayouts, i)->slots;
                }
        }

        class_ctor(ty, class);

        Class *c = class_get(ty, class);
        SynLayout *layout = mrealloc(NULL, sizeof *layout);
        layout->class = class;

        for (usize i = 0; i < n; ++i) {
                i32 id = M_ID(names[i]);
                u16 off = OFF_NOT_FOUND;
                if (id < vN(c->offsets_r)) {
                        off = v__(c->offsets_r, id);
                }
                if (off == OFF_NOT_FOUND || (off >> OFF_SHIFT) != OFF_FIELD) {
                        pthread_mutex_unlock(&SynLock);
                        zP("ty.syntax.tree(): class %s has no field `%s`", c->name, names[i]);
                }
                layout->slots[i] = off & OFF_MASK;
        }

        xvP(SynLayouts, layout);

        return layout->slots;
}

static char const *
syn_kind_name(i32 kind)
{
        usize i = kind - SYNTAX_REGION;
        if (SynKindNames[i] != NULL) {
                return SynKindNames[i];
        }

        char const *raw = syntax_kind_name(kind);
        bool lower = false;

        for (char const *p = raw; *p != '\0'; ++p) {
                lower |= (*p >= 'a' && *p <= 'z');
        }

        byte_vector name = {0};

        if (lower) {
                xvPn(name, raw, strlen(raw));
        } else {
                bool start = true;
                for (char const *p = raw; *p != '\0'; ++p) {
                        if (*p == '_') {
                                start = true;
                                continue;
                        }
                        char c = (*p >= 'A' && *p <= 'Z') ? (*p - 'A' + 'a') : *p;
                        if (start && c >= 'a' && c <= 'z') {
                                c = c - 'a' + 'A';
                        }
                        xvP(name, c);
                        start = false;
                }
        }

        if (kind > STATEMENT_TYPE_START) {
                for (usize k = 0; k < countof(ExprKinds); ++k) {
                        if (strcmp(ExprKinds[k], raw) == 0) {
                                xvPn(name, "Stmt", 4);
                                break;
                        }
                }
        }

        xvP(name, '\0');
        SynKindNames[i] = vv(name);

        return SynKindNames[i];
}

static pthread_rwlock_t SynInternLock = PTHREAD_RWLOCK_INITIALIZER;

static i64
syn_find(char const *s, usize n)
{
        u64 hash = XXH3_64bits(s, n);
        InternBucket const *bucket = &SynInterned.set[hash & (INTERN_TABLE_SIZE - 1)];

        for (usize i = 0; i < vN(*bucket); ++i) {
                InternEntry const *e = v_(*bucket, i);
                if (
                        (e->id >= 0)
                     && (e->hash == hash)
                     && (e->length == n)
                     && (memcmp(e->name, s, n) == 0)
                ) {
                        return e->id;
                }
        }

        return -1;
}

typedef struct {
        char const *s;
        usize n;
        u64 hash;
        i64 id;
} LocalId;

typedef struct {
        LocalId *slots;
        usize cap;
        usize count;
} LocalIds;

static i64
local_id(LocalIds *ids, char const *s, usize n)
{
        if (2 * (ids->count + 1) > ids->cap) {
                LocalIds old = *ids;
                ids->cap = (old.cap == 0) ? 256 : 2 * old.cap;
                ids->slots = mrealloc(NULL, ids->cap * sizeof *ids->slots);
                memset(ids->slots, 0, ids->cap * sizeof *ids->slots);
                ids->count = 0;
                for (usize i = 0; i < old.cap; ++i) {
                        LocalId const *x = &old.slots[i];
                        if (x->s != NULL) {
                                usize h = x->hash & (ids->cap - 1);
                                while (ids->slots[h].s != NULL) {
                                        h = (h + 1) & (ids->cap - 1);
                                }
                                ids->slots[h] = *x;
                                ids->count += 1;
                        }
                }
                xmF(old.slots);
        }

        u64 hash = XXH3_64bits(s, n);
        usize h = hash & (ids->cap - 1);

        while (ids->slots[h].s != NULL) {
                LocalId const *x = &ids->slots[h];
                if (x->hash == hash && x->n == n && memcmp(x->s, s, n) == 0) {
                        return x->id;
                }
                h = (h + 1) & (ids->cap - 1);
        }

        i64 id = -2 - (i64)ids->count;
        ids->slots[h] = (LocalId) { .s = (s == NULL) ? "" : s, .n = n, .hash = hash, .id = id };
        ids->count += 1;

        return id;
}

static i64
syn_text_id(LocalIds *ids, char const *s, usize n)
{
        if (ids == NULL) {
                return intern_n(&SynInterned, s, n)->id;
        }

        i64 id = syn_find(s, n);

        return (id >= 0) ? id : local_id(ids, s, n);
}

// ty/syntax.intern(s: String) -> Int
TY_BUILTIN_RAW(ty_syntax_intern)
{
        ASSERT_ARGC("ty.syntax.intern()", 1);

        Value s = ARGx(0, VALUE_STRING);
        char const *p = (char const *)ss(s);

        pthread_rwlock_rdlock(&SynInternLock);
        i64 id = syn_find(p, sN(s));
        pthread_rwlock_unlock(&SynInternLock);

        if (id < 0) {
                pthread_rwlock_wrlock(&SynInternLock);
                id = intern_n(&SynInterned, p, sN(s))->id;
                pthread_rwlock_unlock(&SynInternLock);
        }

        return INTEGER(id);
}

static isize
block_comment_length(char const *s, isize n)
{
        isize depth = 0;
        isize i = 0;

        while (i < n) {
                if (i + 1 < n && s[i] == '/' && s[i + 1] == '*') {
                        depth += 1;
                        i += 2;
                } else if (i + 1 < n && s[i] == '*' && s[i + 1] == '/') {
                        depth -= 1;
                        i += 2;
                        if (depth == 0) {
                                return i;
                        }
                } else {
                        i += 1;
                }
        }

        return n;
}

inline static bool
line_space(char c)
{
        return c == ' ' || c == '\t' || c == '\f' || c == '\r';
}

inline static bool
raw_byte(u8 c)
{
        return !(c == ' ' || (c >= '\t' && c <= '\r') || c == '/' || c == '#');
}

static isize
until_newline(char const *s, isize n)
{
        isize i = 0;
        while (i < n && s[i] != '\n') {
                i += 1;
        }
        return i;
}

static isize
trivia_piece(char const *s, isize n, int *kind)
{
        if (n >= 2 && s[0] == '/' && s[1] == '*') {
                isize k = block_comment_length(s, n);
                *kind = (n >= 3 && s[2] == '*' && k > 4) ? TRIVIA_DOC : TRIVIA_BLOCK;
                return k;
        }

        if (s[0] == '\n') {
                *kind = TRIVIA_NEWLINE;
                return 1;
        }

        if (n >= 2 && s[0] == '\r' && s[1] == '\n') {
                *kind = TRIVIA_NEWLINE;
                return 2;
        }

        if (line_space(s[0])) {
                isize i = 1;
                while (i < n && line_space(s[i])) {
                        i += 1;
                }
                *kind = TRIVIA_SPACE;
                return i;
        }

        if (n >= 3 && s[0] == '/' && s[1] == '/' && s[2] == '/') {
                *kind = TRIVIA_DOC;
                return until_newline(s, n);
        }

        if (n >= 2 && s[0] == '/' && s[1] == '/') {
                *kind = TRIVIA_COMMENT;
                return until_newline(s, n);
        }

        if (n >= 2 && s[0] == '#' && s[1] == '|') {
                *kind = TRIVIA_DIRECTIVE;
                return until_newline(s, n);
        }

        if (n >= 2 && s[0] == '#' && s[1] == '!') {
                *kind = TRIVIA_SHEBANG;
                return until_newline(s, n);
        }

        if (n >= 3 && (u8)s[0] == 0xEF && (u8)s[1] == 0xBB && (u8)s[2] == 0xBF) {
                *kind = TRIVIA_BOM;
                return 3;
        }

        *kind = TRIVIA_RAW;

        isize i = 0;
        while (i < n && raw_byte(s[i])) {
                i += 1;
        }

        if (i > 0) {
                return i;
        }

        i = 1;
        while (i < n && ((u8)s[i] & 0xC0) == 0x80) {
                i += 1;
        }

        return i;
}

typedef vec(int) KindVec;

typedef struct {
        Ty *ty;
        Value source;
        Value tree;
        int classes[4];
        u16 const *nl;
        u16 const *tl;
        u16 const *vl;
        vec(Value) nodes;
        vec(Value) toks;
} SynBuild;

#define SLOT(o, layout, i) ((o).object->slots[(layout)[(i)]])

static Value
new_node(SynBuild *b, Value kind, i64 start, i64 end, i64 index)
{
        Ty *ty = b->ty;
        Value n = RawObject(b->classes[0]);

        SLOT(n, b->nl, NODE_TREE)   = b->tree;
        SLOT(n, b->nl, NODE_KIND)   = kind;
        SLOT(n, b->nl, NODE_FORM)   = NIL;
        SLOT(n, b->nl, NODE_START)  = INTEGER(start);
        SLOT(n, b->nl, NODE_END)    = INTEGER(end);
        SLOT(n, b->nl, NODE_INDEX)  = INTEGER(index);
        SLOT(n, b->nl, NODE_PARENT) = NIL;
        SLOT(n, b->nl, NODE_NODES)  = ARRAY(vA());
        SLOT(n, b->nl, NODE_CORE)   = ARRAY(vA());
        SLOT(n, b->nl, NODE_SYNTH)  = BOOLEAN(false);
        SLOT(n, b->nl, NODE_OWN)    = ARRAY(vA());
        SLOT(n, b->nl, NODE_FTOK)   = INTEGER(-1);
        SLOT(n, b->nl, NODE_LTOK)   = INTEGER(-2);
        SLOT(n, b->nl, NODE_SYM)    = INTEGER(-1);
        SLOT(n, b->nl, NODE_CALLEE) = INTEGER(-1);
        SLOT(n, b->nl, NODE_TYPE)   = INTEGER(-1);
        SLOT(n, b->nl, NODE_DEF)    = BOOLEAN(false);

        return n;
}

static Value
new_token(SynBuild *b, Value kind, i64 start, i64 end, i64 index)
{
        Ty *ty = b->ty;
        Value t = RawObject(b->classes[1]);

        SLOT(t, b->tl, TOKEN_KIND)     = kind;
        SLOT(t, b->tl, TOKEN_START)    = INTEGER(start);
        SLOT(t, b->tl, TOKEN_END_)     = INTEGER(end);
        SLOT(t, b->tl, TOKEN_TEXT)     = STRING_VIEW(b->source, start, end - start);
        SLOT(t, b->tl, TOKEN_INDEX)    = INTEGER(index);
        SLOT(t, b->tl, TOKEN_OWNER)    = NIL;
        SLOT(t, b->tl, TOKEN_LEADING)  = ARRAY(vA());
        SLOT(t, b->tl, TOKEN_TRAILING) = ARRAY(vA());

        return t;
}

inline static i64
nint(SynBuild const *b, Value n, int field)
{
        return SLOT(n, b->nl, field).z;
}

static void
lex_trivia_into(SynBuild *b, i64 start, i64 end, Array *out, KindVec *kinds)
{
        Ty *ty = b->ty;
        char const *src = (char const *)ss(b->source);

        while (start < end) {
                int kind;
                isize n = trivia_piece(src + start, end - start, &kind);
                Value t = RawObject(b->classes[2]);
                SLOT(t, b->vl, TRIVIA_KIND)  = xSz(TriviaKinds[kind]);
                SLOT(t, b->vl, TRIVIA_START) = INTEGER(start);
                SLOT(t, b->vl, TRIVIA_END)   = INTEGER(start + n);
                SLOT(t, b->vl, TRIVIA_TEXT)  = STRING_VIEW(b->source, start, n);
                vAp(out, t);
                xvP(*kinds, kind);
                start += n;
        }
}

static Array *
int_array(Ty *ty, i64 const *xs, usize n)
{
        Array *a = value_array_new_sized(ty, n);
        for (usize i = 0; i < n; ++i) {
                v__(*a, i) = INTEGER(xs[i]);
        }
        vN(*a) = n;
        return a;
}

typedef vec(i64) IntVec;

// ty/syntax.tree(
//     mod: Module,
//     source: String,
//     tree: _,
//     classes: _,
//     semantic: Bool,
//     error: Int | nil,
//     intern: Bool
// ) -> {lines: Array[Int], packed: Array[Array[Int]], symbols: Array[_]}
TY_BUILTIN_RAW(ty_syntax_tree)
{
        ASSERT_ARGC("ty.syntax.tree()", 7);

        Module *mod    = ARGx(0, VALUE_MODULE).mod;
        Value source   = ARGx(1, VALUE_STRING);
        Value tree     = ARGx(2, VALUE_OBJECT);
        Value classes  = ARGx(3, VALUE_TUPLE);
        bool semantic  = ARGx(4, VALUE_BOOLEAN).boolean;
        Value error_at = ARG(5);
        bool intern    = ARGx(6, VALUE_BOOLEAN).boolean;

        if (classes.count != 4) {
                zP("ty.syntax.tree(): expected (Node, Token, Trivia, Symbol)");
        }

        if (!mod->has_syntax) {
                syntax_snapshot(ty, mod);
        }

        SynBuild b = { .ty = ty, .source = source, .tree = tree };

        for (int i = 0; i < 4; ++i) {
                if (classes.items[i].type != VALUE_CLASS) {
                        zP("ty.syntax.tree(): expected a class");
                }
                b.classes[i] = classes.items[i].class;
        }

        pthread_mutex_lock(&SynLock);
        b.nl = syn_layout(ty, b.classes[0], NodeFields, NODE_SLOTS);
        b.tl = syn_layout(ty, b.classes[1], TokenFields, TOKEN_SLOTS);
        b.vl = syn_layout(ty, b.classes[2], TriviaFields, TRIVIA_SLOTS);
        u16 const *sl = syn_layout(ty, b.classes[3], SymbolFields, SF_SLOTS);
        u16 const *rl = syn_layout(ty, tree.object->class->i, TreeFields, TREE_SLOTS);
        for (isize i = 0; i < vN(mod->syntax); ++i) {
                syn_kind_name(v_(mod->syntax, i)->kind);
        }
        pthread_mutex_unlock(&SynLock);

        GC_STOP();
        SCRATCH_SAVE();

        char const *src = (char const *)ss(source);
        i64 size = sN(source);

        Array *symbols = vA();
        SemInfo info = {0};
        SymVec syms = {0};

        if (semantic) {
                collect_semantics(ty, mod, &info, &syms);
        }

        for (usize i = 0; i < vN(syms); ++i) {
                Symbol const *sym = v__(syms, i);
                Module const *home = sym->mod;
                Value o = RawObject(b.classes[3]);
                SLOT(o, sl, SF_ID)       = INTEGER(sym->symbol);
                SLOT(o, sl, SF_NAME)     = xSz(sym->identifier);
                SLOT(o, sl, SF_KIND)     = xSz(symbol_kind(sym));
                SLOT(o, sl, SF_MODULE)   = (home == NULL || home->name == NULL) ? NIL : xSz(home->name);
                SLOT(o, sl, SF_PATH)     = (home == NULL || home->path == NULL) ? NIL : xSz(home->path);
                SLOT(o, sl, SF_LINE)     = INTEGER(LocLine(sym->loc) + 1);
                SLOT(o, sl, SF_COL)      = INTEGER(LocCol(sym->loc) + 1);
                SLOT(o, sl, SF_BYTE)     = INTEGER(sym->loc.byte);
                SLOT(o, sl, SF_HERE)     = BOOLEAN(home == mod);
                SLOT(o, sl, SF_GLOBAL)   = BOOLEAN(SymbolIsGlobal(sym));
                SLOT(o, sl, SF_PUBLIC)   = BOOLEAN(SymbolIsPublic(sym));
                SLOT(o, sl, SF_BUILTIN)  = BOOLEAN(SymbolIsBuiltin(sym));
                SLOT(o, sl, SF_CAPTURED) = BOOLEAN(SymbolIsCaptured(sym));
                SLOT(o, sl, SF_CONST)    = BOOLEAN(SymbolIsConst(sym));
                SLOT(o, sl, SF_TYPE)     = INTEGER((sym->type == T2_TYPE_INVALID) ? -1 : (i64)sym->type);
                SLOT(o, sl, SF_DOC)      = (sym->doc == NULL) ? NIL : xSz(sym->doc);
                vAp(symbols, o);
        }

        xvF(syms);

        Value root = new_node(&b, xSz("Module"), 0, size, 0);
        Array *nodes = vA();
        Array *every = vA();

        vAp(nodes, root);
        vAp(every, root);

        isize nsyn = vN(mod->syntax);
        vec(i32) owners = {0};

        for (isize i = 0; i < nsyn; ++i) {
                SyntaxNode const *r = v_(mod->syntax, i);
                Value n = new_node(&b, xSz(SynKindNames[r->kind - SYNTAX_REGION]), r->start, r->end, -1);

                if (r->form != NULL) {
                        SLOT(n, b.nl, NODE_FORM) = vSsz(r->form);
                }
                SLOT(n, b.nl, NODE_SYNTH) = BOOLEAN(r->synth);

                if (semantic) {
                        SLOT(n, b.nl, NODE_SYM)    = INTEGER(v__(info.ref, i));
                        SLOT(n, b.nl, NODE_CALLEE) = INTEGER(v__(info.callee, i));
                        SLOT(n, b.nl, NODE_TYPE)   = INTEGER(v__(info.type, i));
                        SLOT(n, b.nl, NODE_DEF)    = BOOLEAN(v__(info.def, i));
                }

                i32 owner = r->parent;
                while (owner >= 0 && v_(mod->syntax, owner)->synth) {
                        owner = v__(owners, owner);
                }
                xvP(owners, owner);

                Value parent = (owner < 0) ? root : v__(b.nodes, owner);
                SLOT(n, b.nl, NODE_PARENT) = parent;

                if (r->synth) {
                        vAp(SLOT(parent, b.nl, NODE_CORE).array, n);
                } else {
                        SLOT(n, b.nl, NODE_INDEX) = INTEGER(vN(*nodes));
                        vAp(SLOT(parent, b.nl, NODE_NODES).array, n);
                        vAp(nodes, n);
                }

                xvP(b.nodes, n);
                vAp(every, n);
        }

        xvF(owners);

        Array *tokens = vA();
        i64 edge = 0;

        for (isize i = 0; i < vN(mod->tokens); ++i) {
                Token const *t = v_(mod->tokens, i);
                if (t->ctx == LEX_FAKE || t->ctx == LEX_HIDDEN || t->type == TOKEN_END) {
                        continue;
                }
                if (
                        (t->type == TOKEN_COMMENT)
                     || (t->type == TOKEN_NEWLINE)
                     || (t->type == TOKEN_DIRECTIVE)
                     || (t->start.byte >= t->end.byte)
                     || ((i64)t->start.byte < edge)
                     || ((i64)t->end.byte > size)
                ) {
                        continue;
                }
                char const *name = token_type_name(t);
                Value kind;
                if (name != NULL) {
                        kind = xSz(name);
                } else if (t->type > 0 && t->type < 0x80) {
                        kind = STRING_VIEW(source, t->start.byte, 1);
                        if (src[t->start.byte] != t->type) {
                                char c = t->type;
                                kind = vSs(&c, 1);
                        }
                } else {
                        kind = xSz("?");
                }
                Value tok = new_token(&b, kind, t->start.byte, t->end.byte, vN(*tokens));
                vAp(tokens, tok);
                edge = t->end.byte;
        }

        if (error_at.type == VALUE_INTEGER) {
                i64 edge = 0;
                Array *top = SLOT(root, b.nl, NODE_NODES).array;
                for (usize i = 0; i < vN(*top); ++i) {
                        edge = max(edge, nint(&b, v__(*top, i), NODE_END));
                }
                i64 start = error_at.z;
                for (usize i = 0; i < vN(*tokens); ++i) {
                        i64 ts = SLOT(v__(*tokens, i), b.tl, TOKEN_START).z;
                        if (ts >= edge) {
                                start = min(ts, start);
                                break;
                        }
                }
                if (start < size) {
                        Value n = new_node(&b, xSz("ParseError"), start, size, vN(*nodes));
                        SLOT(n, b.nl, NODE_PARENT) = root;
                        vAp(top, n);
                        vAp(nodes, n);
                }
        }

        Value eof = new_token(&b, xSz("eof"), size, size, vN(*tokens));

        usize ntok = vN(*tokens);
        KindVec kinds = {0};
        IntVec counts[8] = {0};
        IntVec *lnum = &counts[0], *lnl = &counts[1], *lcm = &counts[2], *lspc = &counts[3];
        IntVec *tnum = &counts[4], *tnl = &counts[5], *tcm = &counts[6], *tspc = &counts[7];
        i64 pos = 0;

        for (usize i = 0; i <= ntok; ++i) {
                Value tok = (i < ntok) ? v__(*tokens, i) : eof;
                i64 start = SLOT(tok, b.tl, TOKEN_START).z;
                Array *pieces = vA();
                v0(kinds);
                lex_trivia_into(&b, pos, max(pos, start), pieces, &kinds);
                usize split = 0;
                if (i > 0) {
                        split = vN(*pieces);
                        for (usize k = 0; k < vN(kinds); ++k) {
                                if (v__(kinds, k) == TRIVIA_NEWLINE) {
                                        split = k + 1;
                                        break;
                                }
                        }
                        Value prev = v__(*tokens, i - 1);
                        Array *trailing = SLOT(prev, b.tl, TOKEN_TRAILING).array;
                        i64 nl = 0, cm = 0, sp = 0;
                        for (usize k = 0; k < split; ++k) {
                                vAp(trailing, v__(*pieces, k));
                                int kind = v__(kinds, k);
                                nl += (kind == TRIVIA_NEWLINE);
                                cm += (kind == TRIVIA_COMMENT || kind == TRIVIA_DOC || kind == TRIVIA_BLOCK);
                                sp += (kind == TRIVIA_SPACE);
                        }
                        xvP(*tnum, split);
                        xvP(*tnl, nl);
                        xvP(*tcm, cm);
                        xvP(*tspc, sp);
                }
                Array *leading = SLOT(tok, b.tl, TOKEN_LEADING).array;
                i64 nl = 0, cm = 0, sp = 0;
                for (usize k = split; k < vN(*pieces); ++k) {
                        vAp(leading, v__(*pieces, k));
                        int kind = v__(kinds, k);
                        nl += (kind == TRIVIA_NEWLINE);
                        cm += (kind == TRIVIA_COMMENT || kind == TRIVIA_DOC || kind == TRIVIA_BLOCK);
                        sp += (kind == TRIVIA_SPACE);
                }
                if (i < ntok) {
                        xvP(*lnum, vN(*pieces) - split);
                        xvP(*lnl, nl);
                        xvP(*lcm, cm);
                        xvP(*lspc, sp);
                }
                pos = SLOT(tok, b.tl, TOKEN_END_).z;
        }

        xvF(kinds);

        vec(Value) stack = {0};
        usize k = 1;
        xvP(stack, root);

        for (usize i = 0; i < ntok; ++i) {
                Value tok = v__(*tokens, i);
                i64 ts = SLOT(tok, b.tl, TOKEN_START).z;
                while (k < vN(*nodes) && nint(&b, v__(*nodes, k), NODE_START) <= ts) {
                        Value n = v__(*nodes, k);
                        i64 ns = nint(&b, n, NODE_START);
                        while (vN(stack) > 1 && nint(&b, *vvL(stack), NODE_END) <= ns) {
                                vN(stack) -= 1;
                        }
                        xvP(stack, n);
                        k += 1;
                }
                while (vN(stack) > 1 && nint(&b, *vvL(stack), NODE_END) <= ts) {
                        vN(stack) -= 1;
                }
                Value owner = *vvL(stack);
                SLOT(tok, b.tl, TOKEN_OWNER) = owner;
                vAp(SLOT(owner, b.nl, NODE_OWN).array, tok);
                for (usize j = 0; j < vN(stack); ++j) {
                        Value n = v__(stack, j);
                        if (nint(&b, n, NODE_FTOK) < 0) {
                                SLOT(n, b.nl, NODE_FTOK) = INTEGER(i);
                        }
                        SLOT(n, b.nl, NODE_LTOK) = INTEGER(i);
                }
        }

        xvF(stack);

        SLOT(tree, rl, TREE_ROOT)   = root;
        SLOT(tree, rl, TREE_NODES)  = ARRAY(nodes);
        SLOT(tree, rl, TREE_EVERY)  = ARRAY(every);
        SLOT(tree, rl, TREE_TOKENS) = ARRAY(tokens);
        SLOT(tree, rl, TREE_EOF)    = eof;

        Array *lines = vA();
        vAp(lines, INTEGER(0));
        for (i64 i = 0; i < size; ++i) {
                if (src[i] == '\n') {
                        vAp(lines, INTEGER(i + 1));
                }
        }
        SLOT(tree, rl, TREE_LINES) = ARRAY(lines);

        usize nn = vN(*nodes);
        IntVec kind = {0}, form = {0}, kstart = {0}, kcount = {0}, kids = {0};
        IntVec ostart = {0}, ocount = {0}, own = {0}, ftok = {0}, ltok = {0};
        IntVec text = {0}, punct = {0}, tstart = {0}, tend = {0}, llen = {0}, tlen = {0};
        IntVec ref = {0}, callee = {0}, type = {0};

        LocalIds local = {0};
        LocalIds *ids = intern ? NULL : &local;

        if (intern) {
                pthread_rwlock_wrlock(&SynInternLock);
        } else {
                pthread_rwlock_rdlock(&SynInternLock);
        }

        for (usize i = 0; i < nn; ++i) {
                Value n = v__(*nodes, i);
                Value kv = SLOT(n, b.nl, NODE_KIND);
                Value fv = SLOT(n, b.nl, NODE_FORM);
                Array *ks = SLOT(n, b.nl, NODE_NODES).array;
                Array *os = SLOT(n, b.nl, NODE_OWN).array;
                xvP(kind, syn_text_id(ids, (char const *)ss(kv), sN(kv)));
                xvP(form, (fv.type == VALUE_STRING) ? syn_text_id(ids, (char const *)ss(fv), sN(fv)) : -1);
                xvP(kstart, vN(kids));
                xvP(kcount, vN(*ks));
                for (usize j = 0; j < vN(*ks); ++j) {
                        xvP(kids, nint(&b, v__(*ks, j), NODE_INDEX));
                }
                xvP(ostart, vN(own));
                xvP(ocount, vN(*os));
                for (usize j = 0; j < vN(*os); ++j) {
                        xvP(own, SLOT(v__(*os, j), b.tl, TOKEN_INDEX).z);
                }
                xvP(ftok, nint(&b, n, NODE_FTOK));
                xvP(ltok, max(nint(&b, n, NODE_LTOK), -1));
                xvP(ref, nint(&b, n, NODE_SYM));
                xvP(callee, nint(&b, n, NODE_CALLEE));
                xvP(type, nint(&b, n, NODE_TYPE));
        }

        for (usize i = 0; i < ntok; ++i) {
                Value tok = v__(*tokens, i);
                Value tv = SLOT(tok, b.tl, TOKEN_TEXT);
                char const *s = (char const *)ss(tv);
                usize n = sN(tv);
                xvP(text, syn_text_id(ids, s, n));
                xvP(punct, n == 1 && (*s == ',' || *s == ';' || *s == '(' || *s == ')'));
                i64 ts = SLOT(tok, b.tl, TOKEN_START).z;
                i64 te = SLOT(tok, b.tl, TOKEN_END_).z;
                Array *lead = SLOT(tok, b.tl, TOKEN_LEADING).array;
                Array *trail = SLOT(tok, b.tl, TOKEN_TRAILING).array;
                xvP(tstart, ts);
                xvP(tend, te);
                xvP(llen, (vN(*lead) == 0) ? 0 : ts - SLOT(v__(*lead, 0), b.vl, TRIVIA_START).z);
                xvP(tlen, (vN(*trail) == 0) ? 0 : SLOT(*vvL(*trail), b.vl, TRIVIA_END).z - te);
        }

        pthread_rwlock_unlock(&SynInternLock);
        xmF(local.slots);

        Value packed = ARRAY(value_array_new_sized(ty, PACKED_FIELDS));
        Packed fields = {
                .kind   = int_array(ty, vv(kind), vN(kind)),
                .form   = int_array(ty, vv(form), vN(form)),
                .kstart = int_array(ty, vv(kstart), vN(kstart)),
                .kcount = int_array(ty, vv(kcount), vN(kcount)),
                .kids   = int_array(ty, vv(kids), vN(kids)),
                .ostart = int_array(ty, vv(ostart), vN(ostart)),
                .ocount = int_array(ty, vv(ocount), vN(ocount)),
                .own    = int_array(ty, vv(own), vN(own)),
                .text   = int_array(ty, vv(text), vN(text)),
                .punct  = int_array(ty, vv(punct), vN(punct)),
                .ftok   = int_array(ty, vv(ftok), vN(ftok)),
                .ltok   = int_array(ty, vv(ltok), vN(ltok)),
                .lnum   = int_array(ty, vv(*lnum), vN(*lnum)),
                .tnum   = int_array(ty, vv(*tnum), vN(*tnum)),
                .lnl    = int_array(ty, vv(*lnl), vN(*lnl)),
                .tnl    = int_array(ty, vv(*tnl), vN(*tnl)),
                .lcm    = int_array(ty, vv(*lcm), vN(*lcm)),
                .tcm    = int_array(ty, vv(*tcm), vN(*tcm)),
                .lspc   = int_array(ty, vv(*lspc), vN(*lspc)),
                .tspc   = int_array(ty, vv(*tspc), vN(*tspc)),
                .tstart = int_array(ty, vv(tstart), vN(tstart)),
                .tend   = int_array(ty, vv(tend), vN(tend)),
                .llen   = int_array(ty, vv(llen), vN(llen)),
                .tlen   = int_array(ty, vv(tlen), vN(tlen)),
                .ref    = int_array(ty, vv(ref), vN(ref)),
                .callee = int_array(ty, vv(callee), vN(callee)),
                .ty     = int_array(ty, vv(type), vN(type))
        };
        i64 sem = semantic;
        fields.sem = int_array(ty, &sem, 1);

        Array **slots = (Array **)&fields;
        for (usize i = 0; i < PACKED_FIELDS; ++i) {
                v__(*packed.array, i) = ARRAY((slots[i] == NULL) ? vA() : slots[i]);
        }
        vN(*packed.array) = PACKED_FIELDS;

        IntVec *all[] = {
                &kind, &form, &kstart, &kcount, &kids, &ostart, &ocount, &own, &ftok,
                &ltok, &text, &punct, &tstart, &tend, &llen, &tlen, &ref, &callee, &type
        };
        for (usize i = 0; i < countof(all); ++i) {
                xvF(*all[i]);
        }
        for (usize i = 0; i < countof(counts); ++i) {
                xvF(counts[i]);
        }

        free_semantics(&info);
        xvF(b.nodes);

        Value result = vTn(
                "lines",   ARRAY(lines),
                "packed",  packed,
                "symbols", ARRAY(symbols)
        );

        SCRATCH_RESTORE();
        GC_RESUME();

        return result;
}

// ty/syntax.lookup(scope: Module | String | nil, path: Array[String]) -> _
TY_BUILTIN_RAW(ty_syntax_lookup)
{
        ASSERT_ARGC("ty.syntax.lookup()", 2);

        Value scope = ARGx(0, VALUE_MODULE, VALUE_STRING, VALUE_NIL);
        Array *path = ARGx(1, VALUE_ARRAY).array;
        Module *mod = scope_module(ty, &scope);

        if (scope.type != VALUE_NIL && mod == NULL) {
                return NIL;
        }

        SCRATCH_SAVE();

        char const **parts = smA(sizeof (char const *) * (vN(*path) + 1));

        for (usize i = 0; i < vN(*path); ++i) {
                Value const *part = v_(*path, i);
                if (part->type != VALUE_STRING) {
                        SCRATCH_RESTORE();
                        return NIL;
                }
                parts[i] = TY_0_C_STR(*part);
        }

        Symbol *sym = compiler_lookup_path(ty, mod, parts, (int)vN(*path));

        SCRATCH_RESTORE();

        return (symbol_id(sym) < 0) ? NIL : symbol_record(ty, sym, NULL);
}

// ty/syntax.resolve-type(text: String, scope: Module | String | nil = nil) -> Int | nil
TY_BUILTIN_RAW(ty_syntax_resolve_type)
{
        ASSERT_ARGC("ty.syntax.resolve-type()", 1, 2);

        Value text  = ARGx(0, VALUE_STRING);
        Value scope = (argc > 1) ? ARGx(1, VALUE_MODULE, VALUE_STRING, VALUE_NIL) : NIL;
        Module *mod = scope_module(ty, &scope);

        T2Type t = compiler_resolve_type_text(ty, mod, TY_0_C_STR(text));

        return (t == T2_TYPE_INVALID) ? NIL : INTEGER(t);
}

// ty/syntax.show-type(type: Int) -> String
TY_BUILTIN_RAW(ty_syntax_show_type)
{
        ASSERT_ARGC("ty.syntax.show-type()", 1);

        i64 t = ARGx(0, VALUE_INTEGER).z;

        if (t <= 0) {
                return vSsz("_");
        }

        return xSz(t2_show(ty, (T2Type)t));
}

// ty/syntax.type-value(type: Int) -> _
TY_BUILTIN_RAW(ty_syntax_type_value)
{
        ASSERT_ARGC("ty.syntax.type-value()", 1);

        i64 t = ARGx(0, VALUE_INTEGER).z;

        return (t <= 0) ? NIL : t2_to_ty(ty, (T2Type)t);
}

static Value
relation(T2Relation r)
{
        switch (r) {
        case T2_RELATION_YES: return BOOLEAN(true);
        case T2_RELATION_NO:  return BOOLEAN(false);
        default:              return NIL;
        }
}

// ty/syntax.subtype?(sub: Int, sup: Int, gradual: Bool = false) -> Bool | nil
TY_BUILTIN_RAW(ty_syntax_subtype)
{
        ASSERT_ARGC("ty.syntax.subtype?()", 2, 3);

        i64 a = ARGx(0, VALUE_INTEGER).z;
        i64 b = ARGx(1, VALUE_INTEGER).z;
        bool gradual = (argc > 2) && value_truthy(ty, &ARG(2));

        if (a <= 0 || b <= 0) {
                return NIL;
        }

        T2Universe *universe = t2_global_universe();

        return relation(
                gradual ? t2_gradual_subtype(universe, (T2Type)a, (T2Type)b)
                        : t2_subtype(universe, (T2Type)a, (T2Type)b)
        );
}

static Module const *
source_module(Ty *ty, char const *s)
{
        ModuleVector const *mods = TyActiveModules(ty);

        for (usize i = 0; i < vN(*mods); ++i) {
                Module const *mod = v__(*mods, i);
                if (mod->source == NULL) {
                        continue;
                }
                if (s >= mod->source && s <= mod->source + strlen(mod->source)) {
                        return mod;
                }
        }

        return NULL;
}

// ty/syntax.member(type: Int, name: String, home: Module | nil = nil) -> _
TY_BUILTIN_RAW(ty_syntax_member)
{
        ASSERT_ARGC("ty.syntax.member()", 2, 3);

        i64 t = ARGx(0, VALUE_INTEGER).z;
        Value name = ARGx(1, VALUE_STRING);
        Value home = (argc > 2) ? ARGx(2, VALUE_MODULE, VALUE_NIL) : NIL;

        if (t <= 0) {
                return NIL;
        }

        Expr const *e = t2_find_member(ty, (T2Type)t, TY_0_C_STR(name));

        if (e == NULL) {
                return NIL;
        }

        bool method = (e->type == EXPRESSION_FUNCTION);
        Class const *owner = (method && xF(e, class) != NULL) ? xF(e, class) : t2_class_of(ty, (T2Type)t);
        Module const *mod = source_module(ty, LocS(e->start));

        if (
                (mod == NULL)
             && (home.type == VALUE_MODULE)
             && (home.mod->source != NULL)
             && (LocS(e->start) >= home.mod->source)
             && (LocS(e->start) <= home.mod->source + strlen(home.mod->source))
        ) {
                mod = home.mod;
        }

        return vTn(
                "name",  name,
                "kind",  xSz(method ? "method" : "field"),
                "owner", (owner == NULL) ? NIL : xSz(class_name(ty, owner->i)),
                "path",  (mod == NULL || mod->path == NULL) ? NIL : xSz(mod->path),
                "line",  INTEGER(LocLine(e->start) + 1),
                "col",   INTEGER(LocCol(e->start) + 1),
                "byte",  INTEGER(e->start.byte),
                "type",  INTEGER((e->_type == T2_TYPE_INVALID) ? -1 : (i64)e->_type),
                "doc",   (method && xF(e, doc) != NULL) ? xSz(xF(e, doc)) : NIL
        );
}
