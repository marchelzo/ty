#include "ty.h"
#include "types.h"
#include "class.h"
#include "intern.h"
#include "ast.h"
#include "compiler.h"
#include "operators.h"
#include "value.h"

#undef NIL

#define ANY TYPE_ANY
#define NIL NIL_TYPE

#define CloneVec(v) (                                  \
        (v).items = memcpy(                            \
                mA((v).capacity * sizeof *(v).items),  \
                (v).items,                             \
                (v).count * sizeof *(v).items          \
        )                                              \
)

static Expr *
FindMethod(Class const *c, char const *name);

static Type *
TypeOf2Op(Ty *ty, int op, Type *t0, Type *t1);

static void
BindVars(Ty *ty, Type *t0, Type *t1);

static bool
BindConstraint(Ty *ty, Constraint const *c);

static Type *
ResolveAlias(Ty *ty, Type *t0);

bool
type_check_x(Ty *ty, Type *t0, Type *t1, bool bind);

Value *
vm_local(Ty *ty, int i);

Type *TYPE_INT;
Type *TYPE_FLOAT;
Type *TYPE_BOOL;
Type *TYPE_STRING;
Type *TYPE_BLOB;
Type *TYPE_ARRAY;
Type *TYPE_DICT;
Type *NIL_TYPE;
Type *TYPE_ANY;
Type *TYPE_CLASS_;

static Type ZERO = { .type = TYPE_INTEGER, .z = 0 };

static Type *
NewType(Ty *ty, int t)
{
        Type *type = amA0(sizeof *type);
        type->type = t;
        return type;
}

static Scope *
FunTypeScope(Ty *ty)
{
        Scope *s = ty->tscope;

        while (s != NULL && s->function != s) {
                s = s->parent;
        }

        return s;
}

static Symbol *
InsertFunTypeVar(Ty *ty, Symbol *var)
{
        scope_insert(ty, FunTypeScope(ty), var);
}

static Scope *
GlobalTypeScope(Ty *ty)
{
        Scope *s = ty->tscope;

        if (s == NULL) {
                return ty->tscope = scope_new(ty, "", NULL, true);
        }

        while (s->parent != NULL) {
                s = s->parent;
        }

        return s;
}

static Type *
AddParam(Ty *ty, Type *t0)
{
        char b[32];
        Symbol *var;

        snprintf(b, sizeof b, "$%d", (int)vN(t0->params));
        var = NewTypeVar(ty, sclonea(ty, b));

        avP(t0->params, var);

        return var->type;
}

static Type *
AddScopedParam(Ty *ty, Type *t0)
{
        char b[32];
        Symbol *var;

        snprintf(b, sizeof b, "$%d", (int)vN(t0->params));
        var = NewScopedTypeVar(ty, FunTypeScope(ty), sclonea(ty, b));

        avP(t0->params, var);

        return var->type;
}

static Type *
GenVar2(Ty *ty)
{
        static int sym = 0;

        char b[32];
        Symbol *var;

        snprintf(b, sizeof b, "<t%d>", ++sym);
        var = scope_add_type_var(ty, GlobalTypeScope(ty), sclonea(ty, b));

        return var->type;
}

static Type *
GenVar(Ty *ty)
{
        if (
                TyCompilerState(ty)->func == NULL
             || TyCompilerState(ty)->func->_type == NULL
        ) {
                return GenVar2(ty);
        }

        Type *ft = TyCompilerState(ty)->func->_type;

        return AddParam(ty, ft);
}

static Type *
GenScopedVar(Ty *ty)
{
        if (
                TyCompilerState(ty)->func == NULL
             || TyCompilerState(ty)->func->_type == NULL
        ) {
                return GenVar2(ty);
        }

        Type *ft = TyCompilerState(ty)->func->_type;

        return AddScopedParam(ty, ft);
}

static Type *
CloneType(Ty *ty, Type *t0)
{
        Type *t;

        if (t0 == NULL) {
                t = NULL;
        } else {
                t = amA(sizeof *t);
                *t = *t0;
        }

        return t;
}

inline static int
UnionCount(Type const *t0)
{
        return (t0 == NULL || t0->type != TYPE_UNION) ? 1 : vN(t0->types);
}

inline static Type *
UnionElem(Type const *t0, int i)

{
        if (
                t0 == NULL
             || t0->type != TYPE_UNION
             || vN(t0->types) <= i
        ) {
                return (Type *)t0;
        } else {
                return v__(t0->types, i);
        }
}

inline static Type **
UnionElemPtr(Type **t0, int i)

{
        if (
                *t0 == NULL
             || (*t0)->type != TYPE_UNION
             || vN((*t0)->types) <= i
        ) {
                return (Type **)t0;
        } else {
                return v_((*t0)->types, i);
        }
}

inline static int
IntersectCount(Type const *t0)
{
        return (t0 == NULL || t0->type != TYPE_INTERSECT) ? 1 : vN(t0->types);
}

inline static Type *
IntersectElem(Type const *t0, int i)

{
        if (
                t0 == NULL
             || t0->type != TYPE_INTERSECT
             || vN(t0->types) <= i
        ) {
                return (Type *)t0;
        } else {
                return v__(t0->types, i);
        }
}

inline static bool
IsAny(Type *t0)
{
        return t0 != NULL
            && t0->type == TYPE_OBJECT
            && t0->class->i == CLASS_TOP;
}

inline static bool
NullOrAny(Type *t0)
{
        return t0 == NULL || IsAny(t0);
}

inline static bool
IsNil(Type *t0)
{
        return t0 != NULL
            && t0->type == TYPE_OBJECT
            && t0->class->i == CLASS_NIL;
}

inline static Type *
ReturnType(Expr const *f)
{
        return (f != NULL && f->_type != NULL)
             ? f->_type->rt
             : NULL;
}

inline static bool
IsTagged(Type const *t0)
{
        return t0 != NULL
            && t0->type == TYPE_OBJECT
            && t0->class->def != NULL
            && t0->class->def->type == STATEMENT_TAG_DEFINITION;
}

inline static int
TagOf(Type const *t0)
{
        return (IsTagged(t0) || t0->type == TYPE_TAG)
             ? t0->class->def->tag.symbol
             : -1;
}

inline static int
ArgCount(Type const *t0)
{
        if (t0 == NULL) {
                return 0;
        }

        switch (t0->type) {
        case TYPE_TUPLE:
        case TYPE_UNION:
        case TYPE_INTEGER:
        case TYPE_NIL:
                return 0;
        }

        return vN(t0->args);
}

inline static Type *
TypeArg(Type *t0, int i)
{
        if (
                t0 == NULL
             || (
                        t0->type != TYPE_OBJECT
                     && t0->type != TYPE_CLASS
                     && t0->type != TYPE_FUNCTION
                )
             || (int)vN(t0->args) <= i
             || (
                        i < 0
                     && (int)vN(t0->args) <= (i += vN(t0->args))
                )
        ) {
                return NULL;
        }

        return v__(t0->args, i);
}

inline static Type *
RecordField(Ty *ty, Type *t0, char const *name)
{
        if (t0 == NULL) {
                return NULL;
        }

        Type *t1;
        Type *t2;

        switch (t0->type) {
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        char const *name0 = v__(t0->names, i);
                        if (name0 != NULL && strcmp(name0, name) == 0) {
                                return v__(t0->types, i);
                        }
                }
                return NULL;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = RecordField(ty, v__(t0->types, i), name);
                        if (t1 != NULL) {
                                return t1;
                        }
                }
                return NULL;

        case TYPE_UNION:
                t2 = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = RecordField(ty, v__(t0->types, i), name);
                        unify(ty, &t2, t1);
                }
                return t2;

        case TYPE_OBJECT:
                return type_member_access_t(ty, t0, name);
        }

        return NULL;
}

inline static Type *
RecordElem(Type *t0, int i)
{
        if (
                t0 == NULL
             || (t0->type != TYPE_TUPLE && t0->type != TYPE_UNION)
             || vN(t0->types) <= i
        ) {
                return NULL;
        }

        return v__(t0->types, i);
}

static Expr *
FieldIdentifier(Expr const *field)
{
        if (field == NULL) {
                return NULL;
        }

        if (field->type == EXPRESSION_IDENTIFIER) {
                return (Expr *)field;
        }

        if (
                field->type == EXPRESSION_EQ
             && field->target->type == EXPRESSION_IDENTIFIER
        ) {
                return field->target;
        }

        return NULL;
}

static bool
IsConcrete(Type *t0)
{
        if (NullOrAny(t0)) {
                return true;
        }

        switch (t0->type) {
        case TYPE_VARIABLE:
                return false;

        case TYPE_UNION:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!IsConcrete(v__(t0->types, i))) {
                                return false;
                        }
                }
                return true;

        case TYPE_CLASS:
        case TYPE_OBJECT:
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (!IsConcrete(v__(t0->args, i))) {
                                return false;
                        }
                }
                return true;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (!IsConcrete(v__(t0->args, i))) {
                                return false;
                        }
                }
                if (!IsConcrete(t0->rt)) {
                        return false;
                }
                return true;


        case TYPE_INTEGER:
        case TYPE_NIL:
                return true;
        }

        return true;
}

static int
ClassOfType(Ty *ty, Type *t0)
{
        if (NullOrAny(t0)) {
                return CLASS_TOP;
        }

        int class;

        switch (t0->type) {
        case TYPE_UNION:
                class = ClassOfType(ty, v__(t0->types, 0));
                for (int i = 1; i < vN(t0->types); ++i) {
                        int c = ClassOfType(ty, v__(t0->types, i));
                        if (c == class)
                                continue;
                        if (class_is_subclass(ty, class, c))
                                class = c;
                        else if (!class_is_subclass(ty, c, class))
                                return CLASS_TOP;
                }
                return class;

        case TYPE_OBJECT:
                return t0->class->i;

        case TYPE_CLASS:
                return CLASS_CLASS;

        case TYPE_INTEGER:
                return CLASS_INT;
        }

        return CLASS_TOP;
}

static Type *
UnionOf(Ty *ty, Type *t0)
{
        if (NullOrAny(t0)) {
                return NULL;
        }

        Type *t = NULL;
        Class *c;

        switch (t0->type) {
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify(ty, &t, v__(t0->types, i));
                }
                break;

        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify(ty, &t, UnionOf(ty, v__(t0->types, i)));
                }
                break;

        case TYPE_OBJECT:
                c = class_get_class(ty, ClassOfType(ty, t0));
                for (int i = 0; i < vN(c->fields.values); ++i) {
                        Value const *field = v_(c->fields.values, i);
                        unify(
                                ty,
                                &t,
                                (
                                        (field->extra != NULL)
                                      ? type_resolve(ty, field->extra)
                                      : ((Expr *)field->ptr)->_type
                                )
                        );

                }
                break;

        default:
                return NULL;
        }

        return t;
}

Type *
type_object(Ty *ty, Class *class)
{
        Type *t = NewType(ty, TYPE_OBJECT);
        t->class = class;

        return t;
        if (class->def != NULL) {
                for (int i = 0; i < vN(class->def->class.type_params); ++i) {
                        Type *t0 = type_resolve(
                                ty,
                                v__(class->def->class.type_params, i)
                        );
                        avP(
                                t->params,
                                t0->var
                        );
                        avP(t->args, t0);
                }
        }

        dont_printf("type_object(%s) = %s (narg=%d)\n", class->name, type_show(ty, t), (int)vN(t->args));

        return t;
}

Type *
type_variable(Ty *ty, Symbol *var)
{
        Type *t = NewType(ty, TYPE_VARIABLE);
        t->var = var;
        return t;
}

Type *
type_integer(Ty *ty, intmax_t z)
{
        Type *t = NewType(ty, TYPE_INTEGER);
        t->z = z;
        return t;
}

Type *
type_type(Ty *ty, Type *t0)
{
        Type *t = NewType(ty, TYPE_TYPE);
        t->_type = t0;
        return t;
}

Type *
type_alias(Ty *ty, Stmt const *def)
{
        Type *t = NewType(ty, TYPE_ALIAS);

        for (int i = 0; i < vN(def->class.type_params); ++i) {
                Type *t0 = type_resolve(
                        ty,
                        v__(def->class.type_params, i)
                );
                avP(
                        t->params,
                        t0->var
                );
        }

        t->name = def->class.name;
        t->_type = type_resolve(ty, def->class.type);

        return t;
}

Type *
type_tag(Ty *ty, Class *class)
{
        Type *t = NewType(ty, TYPE_TAG);
        t->class = class;
        
        Type *t0 = GenVar(ty);
        avP(t->params, t0->var);

        return t;
}

Type *
type_class(Ty *ty, Class *class)
{
        Type *t = NewType(ty, TYPE_CLASS);
        t->class = class;

        if (class->def != NULL) {
                for (int i = 0; i < vN(class->def->class.type_params); ++i) {
                        Type *t0 = type_resolve(
                                ty,
                                v__(class->def->class.type_params, i)
                        );
                        avP(
                                t->params,
                                t0->var
                        );
                }
        }

        return t;
}

Type *
type_function(Ty *ty, Expr const *e)
{
        Type *t = NewType(ty, TYPE_FUNCTION);

        dont_printf("================== %s ======================\n", e->name);

        if (e->return_type != NULL) {
                t->rt = type_fixed(ty, type_resolve(ty, e->return_type));
        }

        for (int i = 0; i < vN(e->type_params); ++i) {
                avP(t->params, v__(e->type_params, i)->symbol);
        }

        for (int i = vN(e->type_params); i < vN(e->param_symbols); ++i) {
                Symbol *psym = v__(e->param_symbols, i);
                if (psym->type == NULL) {
                        psym->type = AddParam(ty, t);
                }
        }
        
        for (int i = 0; i < vN(e->param_symbols); ++i) {
                avP(
                        t->fun_params,
                        PARAM(
                                v__(e->param_symbols, i),
                                v__(e->param_symbols, i)->type
                        )
                );
        }

        return t;
}

static Type *
Relax(Type *t0)
{
        if (t0 != NULL) switch (t0->type) {
        case TYPE_INTEGER:
                return TYPE_INT;
        }

        return t0;
}

inline static Type *
EnvParamLookup(ParamVector const *env, Symbol const *var)
{
        for (int i = 0; i < vN(*env); ++i) {
                if (v_(*env, i)->var == var) {
                        return v_(*env, i)->type;
                }
        }

        return var->type;
}

inline static void
EnvParamUpdate(ParamVector const *env, Symbol const *var, Type *t0)
{
        for (int i = 0; i < vN(*env); ++i) {
                if (v_(*env, i)->var == var) {
                        v_(*env, i)->type = t0;
                        return;
                }
        }
}

inline static Symbol *
EnvLookup(symbol_vector const *env, Symbol const *var)
{
        for (int i = 0; i < vN(*env); ++i) {
                if (v__(*env, i) == var) {
                        return v__(*env, i);
                }
        }

        return NULL;
}

static Type *
Propagate(Ty *ty, Type *t0)
{
        static int d = 0;

        dont_printf("%*sPropagate(%s)\n", 4*d, "", type_show(ty, t0));

        if (t0 == NULL) {
                return NULL;
        }

        d += 1;

        Symbol *var;
        Type *t1;
        Type *t2;
        bool cloned = false;

        Type *t_ = t0;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (t0->mark) {
                        goto ShortCircuit;
                } else {
                        t0->mark = true;
                }
                var = scope_find_symbol(ty->tscope, t0->var);
                if (var == NULL) {
                        if (t0->var->type != t0) {
                                t2 = Propagate(ty, t0->var->type);
                        } else {
                                break;
                        }
                } else if (var->type == t0) {
                        break;
                } else {
                        t2 = Propagate(ty, var->type);
                }
                t1 = t0;
                t0 = CloneType(ty, t2);
                for (int i = 0; i < vN(t1->args); ++i) {
                        avP(t0->args, Propagate(ty, v__(t1->args, i)));
                }
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        t2 = Propagate(ty, t1);
                        if (t2 != t1 && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->types);
                                cloned = true;
                        }
                        *v_(t0->types, i) = t2;
                }
                break;

        case TYPE_OBJECT:
                for (int i = 0; i < vN(t0->args); ++i) {
                        t1 = v__(t0->args, i);
                        t2 = Propagate(ty, t1);
                        if (t2 != t1 && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->args);
                                cloned = true;
                        }
                        *v_(t0->args, i) = t2;
                }
                for (int i = vN(t0->args); i < vN(t0->params); ++i) {
                        var = scope_find_symbol(ty->tscope, v__(t0->params, i));
                        avP(t0->args, (var != NULL) ? var->type : v__(t0->params, i)->type);
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_ALIAS:
                if (vN(t0->args) == vN(t0->params)) {
                        t0 = ResolveAlias(ty, t0);
                }
                break;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        t1 = Propagate(ty, p->type);
                        if (t1 != p->type && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->fun_params);
                                cloned = true;
                        }
                        *v_(t0->fun_params, i) = PARAM(p->var, t1);
                }
                t1 = Propagate(ty, t0->rt);
                if (t1 != t0->rt && !cloned) {
                        t0 = CloneType(ty, t0);
                }
                t0->rt = t1;
                break;
        }

        if (t_->type == TYPE_VARIABLE) {
                t_->mark = false;
        }

ShortCircuit:
        d -= 1;

        dont_printf("%*sPropagate(%s) => %s\n", d*4, "", type_show(ty, t_), type_show(ty, t0));

        return t0;
}

static void
BindVars(Ty *ty, Type *t0, Type *t1)
{
        Symbol *var;
        Type *t2;

        dont_printf("BindVar():\n  %s\n  %s\n", type_show(ty, t0), type_show(ty, t1));

        t0 = Propagate(ty, t0);
        t1 = Propagate(ty, t1);

        if (t0 == NULL || t1 == NULL) {
                return;
        }

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (vN(t0->args) == 0) {
                        var = scope_find_symbol(ty->tscope, t0->var);
                        if (var == NULL || var == t0->var) {
                                var = scope_insert(ty, ty->tscope, t0->var);
                                var->type = CloneType(ty, t1);
                                if (var->type != NULL) {
                                        v0(var->type->args);
                                }
                                var->type = Relax(Propagate(ty, t1));
                        }
                        //unify(ty, &var->type, Relax(Propagate(ty, t1)));
                        dont_printf("BindVar(): %s := %s\n", var->identifier, type_show(ty, var->type));
                } else {
                        int extra = ArgCount(t1) - ArgCount(t0);
                        for (int i = 0; i < vN(t0->args); ++i) {
                                BindVars(
                                        ty,
                                        v__(t0->args, i),
                                        TypeArg(t1, i - vN(t0->args))
                                );
                        }
                        var = scope_find_symbol(ty->tscope, t0->var);
                        if (var == NULL || var->type == t0) {
                                var = scope_insert(ty, ty->tscope, t0->var);
                                var->type = NULL;
                        }
                        if (extra < ArgCount(t1)) {
                                t2 = CloneType(ty, t1);
                                v0(t2->args);
                                avPvn(t2->args, t1->args, extra);
                                t1 = t2;
                        }
                        unify(ty, &var->type, Relax(Propagate(ty, t1)));
                        dont_printf("BindVar(): %s := %s\n", var->identifier, type_show(ty, var->type));
                }
                break;

        case TYPE_OBJECT:
                for (int i = 0; i < ArgCount(t0) && i < ArgCount(t1); ++i) {
                        BindVars(ty, TypeArg(t0, i), TypeArg(t1, i));
                }
                if (t0->class->i >= CLASS_PRIMITIVE) {
                        ClassDefinition *def = &t0->class->def->class;
                        for (int i = 0; i < vN(def->fields); ++i) {
                                Expr *field = v__(def->fields, i);
                                Expr *id = (field->type == EXPRESSION_EQ)
                                         ? field->target
                                         : field;
                                Type *t = (id->constraint != NULL)
                                        ? type_resolve(ty, id->constraint)
                                        : field->value->_type;
                                BindVars(
                                        ty,
                                        t,
                                        type_member_access_t(ty, t0, field->identifier)
                                );
                        }
                        for (int i = 0; i < vN(def->methods); ++i) {
                                // TODO
                        }
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_UNION:
                break;

        case TYPE_TUPLE:
                if (t1 != NULL && t1->type == TYPE_TUPLE) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                char const *name = v__(t0->names, i);
                                t2 = (name != NULL)
                                   ? RecordField(ty, t1, name)
                                   : RecordElem(t1, i);
                                if (t2 != NULL) {
                                        BindVars(ty, v__(t0->types, i), t2);
                                }
                        }
                        for (int i = 0; i < vN(t1->types); ++i) {
                                char const *name = v__(t1->names, i);
                                t2 = (name != NULL)
                                   ? RecordField(ty, t0, name)
                                   : RecordElem(t0, i);
                                if (t2 != NULL) {
                                        BindVars(ty, v__(t0->types, i), t2);
                                }
                        }
                } else if (t1 != NULL && t1->type == TYPE_OBJECT) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                char const *name = v__(t0->names, i);
                                t2 = (name != NULL)
                                   ? type_member_access_t(ty, t1, name)
                                   : NULL;
                                if (t2 != NULL) {
                                        BindVars(ty, v__(t0->types, i), t2);
                                }
                        }
                }
                break;

        //                        T  -> U
        //  ($0 * Float -> $1) => $0 -> $1

        case TYPE_FUNCTION:
                if (t1 != NULL && t1->type == TYPE_FUNCTION) {
                        for (int i = 0; i < vN(t0->fun_params); ++i) {
                                Type *t2 = (vN(t1->fun_params) > i) ? v_(t1->fun_params, i)->type : NIL_TYPE;
                                BindVars(ty, v_(t0->fun_params, i)->type, t2);
                        }
                        for (int i = 0; i < vN(t1->fun_params); ++i) {
                                Type *t2 = (vN(t0->fun_params) > i) ? v_(t0->fun_params, i)->type : NIL_TYPE;
                                BindVars(ty, v_(t1->fun_params, i)->type, t2);
                        }
                        for (int i = 0; i < vN(t0->constraints); ++i) {
                                BindConstraint(ty, v_(t0->constraints, i));
                        }
                        for (int i = 0; i < vN(t1->constraints); ++i) {
                                BindConstraint(ty, v_(t1->constraints, i));
                        }
                        BindVars(ty, t0->rt, t1->rt);
                } else if (t1->type == TYPE_VARIABLE) {
                        var = scope_find_symbol(ty->tscope, t1->var);
                        if (var == NULL || var->type == t1) {
                                var = scope_insert(
                                        ty,
                                          (t1->var->scope == NULL)
                                        ? FunTypeScope(ty)
                                        : ty->tscope,
                                        t1->var
                                );
                                var->type = t0;
                        }
                }
                break;
        }
}

static bool
BindConstraint(Ty *ty, Constraint const *c)
{
        Type *t0;
        Type *t1;
        Type *t2;

        switch (c->type) {
        case TC_2OP:
                t0 = Propagate(ty, c->t0);
                t1 = Propagate(ty, c->t1);
                t2 = Propagate(ty, c->rt);
                dont_printf(
                        "BindConstraint(TC_2OP):\n  t0=%s\n  t1=%s\n  t2=%s\n",
                        type_show(ty, t0),
                        type_show(ty, t1),
                        type_show(ty, t2)
                );
                if (
                        IsConcrete(t0)
                     && IsConcrete(t1)
                     && IsConcrete(t2)
                ) {
                        puts("All concrete.");
                        return true;
                }
                if (
                        IsConcrete(t0)
                     && IsConcrete(t1)
                ) {
                        BindVars(
                                ty,
                                t2,
                                Propagate(ty, TypeOf2Op(ty, c->op, t0, t1))
                        );

                        return true;
                }
                break;
        }

        return true;
}

static Type *
ResolveAlias(Ty *ty, Type *t0)
{
        ty->tscope = scope_new(ty, "", ty->tscope, false);

        //char const *s0 = type_show(ty, t0);

        for (int i = 0; i < vN(t0->args) && i < vN(t0->params); ++i) {
                BindVars(ty, v__(t0->params, i)->type, v__(t0->args, i));
        }

        Type *t = Propagate(ty, t0->_type);

        dont_printf("ResolveAlias(%s) = %s\n", type_show(ty, t0), type_show(ty, t));

        ty->tscope = ty->tscope->parent;

        return t;

}

static bool
CheckCall(Ty *ty, expression_vector const *args, Type *t0)
{
        Type *t1;
        Type *t2;
        Expr *init;

        dont_printf("CheckCall(%s)\n", type_show(ty, t0));
        for (int i = 0; i < vN(*args); ++i) {
                dont_printf("    %s\n", type_show(ty, v__(*args, i)->_type));
        }

        if (t0 == NULL) {
                return true;
        }

        switch (t0->type) {
        case TYPE_FUNCTION:
                if (vN(*args) > vN(t0->fun_params)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        t1 = v_(t0->fun_params, i)->type;
                        t2 = (vN(*args) > i) ? v__(*args, i)->_type : NIL_TYPE;
                        if (!type_check_x(ty, t1, t2, false)) {
                                return false;
                        }
                }
                return true;

        case TYPE_CLASS:
                init = FindMethod(t0->class, "init");
                if (init == NULL) {
                        return true;
                }
                t1 = init->_type;
                return (t1 == NULL) ? true : CheckCall(ty, args, t1);

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        if (CheckCall(ty, args, t1)) {
                                return true;
                        }
                }
        }

        return true;
}

static Type *
BindCall(Ty *ty, expression_vector const *args, Type *t0)
{
        Type *t1;
        Type *t2;
        Expr *init;

        dont_printf("BindCall(%s)\n", type_show(ty, t0));
        for (int i = 0; i < vN(*args); ++i) {
                dont_printf("    %s\n", type_show(ty, v__(*args, i)->_type));
        }

        if (t0 == NULL) {
                return NULL;
        }

        switch (t0->type) {
        case TYPE_FUNCTION:
                for (int i = 0; i < vN(*args) && i < vN(t0->fun_params); ++i) {
                        BindVars(ty, v_(t0->fun_params, i)->var->type, v__(*args, i)->_type);
                }
                for (int i = vN(*args); i < vN(t0->fun_params); ++i) {
                        BindVars(ty, v_(t0->fun_params, i)->var->type, NIL_TYPE);
                }
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        BindConstraint(ty, v_(t0->constraints, i));
                }
                return t0->rt;

        case TYPE_CLASS:
                init = FindMethod(t0->class, "init");
                if (init == NULL) {
                        break;
                }

                t1 = init->_type;
                if (t1 != NULL) {
                        BindCall(ty, args, t1);
                }
                return t0->class->object_type;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        if (CheckCall(ty, args, t1)) {
                                return BindCall(ty, args, t1);
                        }
                }
        }

        return NULL;
}

static Type *
SolveCall(Ty *ty, expression_vector const *args, Type *t0)
{
        Type *t;

        ty->tscope = scope_new(ty, "", ty->tscope, false);
        t = Propagate(ty, BindCall(ty, args, t0));
        ty->tscope = ty->tscope->parent;

        return t;
}

static Type *
type_call_t(Ty *ty, Expr const *e, Type *t0)
{
        if (NullOrAny(t0)) {
                return ANY;
        }

        if (IsNil(t0)) {
                return NIL;
        }

        Type *t;
        Symbol *var;
        expression_vector const *args;

        switch (e->type) {
        case EXPRESSION_FUNCTION_CALL:
                args = &e->args;
                break;
        case EXPRESSION_METHOD_CALL:
                args = &e->method_args;
                break;
        default:
                args = &(expression_vector){0};
        }

        switch (t0->type) {
        case TYPE_FUNCTION:
        case TYPE_CLASS:
        case TYPE_INTERSECT:
                return Propagate(ty, SolveCall(ty, args, t0));

        case TYPE_TAG:
                t = NewType(ty, TYPE_OBJECT);
                t->class = t0->class;
                switch (e->type) {
                case EXPRESSION_FUNCTION_CALL:
                case EXPRESSION_METHOD_CALL:
                        avP(t->args, (vN(*args) == 0) ? NULL : v__(*args, 0)->_type);
                        break;
                case EXPRESSION_TAG_APPLICATION:
                        avP(t->args, e->tagged->_type);
                        break;
                default:
                        avP(t->args, NULL);
                }
                return t;

        case TYPE_UNION:
                t = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify(ty, &t, type_call_t(ty, e, v__(t0->types, i)));
                }
                return t;

        case TYPE_OBJECT:
                switch (t0->class->i) {
                case CLASS_ARRAY:
                        // FIXME Maybe
                        return TypeArg(t0, 0);
                case CLASS_DICT:
                        // FIXME Maybe
                        return TypeArg(t0, 1);
                }
                break;

        case TYPE_VARIABLE:
                dont_printf("(0) %s\n", t0->var->identifier);
                var = scope_find_symbol(ty->tscope, t0->var);
                if (var == NULL || var->type == t0) {
                        var = scope_insert(
                                ty,
                                (t0->var->scope == NULL) ? FunTypeScope(ty) : ty->tscope,
                                t0->var
                        );
                        var->type = NewType(ty, TYPE_FUNCTION);
                        var->type->rt = GenScopedVar(ty);
                        for (int i = 0; i < vN(*args); ++i) {
                                avP(
                                        var->type->fun_params,
                                        PARAM(NULL, v__(*args, i)->_type)
                                );
                        }
                        dont_printf("(1) %s := %s\n", t0->var->identifier, type_show(ty, t0->var->type));
                        dont_printf("(2) %s := %s\n", var->identifier, type_show(ty, var->type));
                        return var->type->rt;
                }
        }

        return NULL;
}

Type *
type_call(Ty *ty, Expr const *e)
{
        Type *t0 = type_call_t(ty, e, e->function->_type);
        dont_printf("type_call()\n");
        dont_printf("    >>> %s\n", show_expr(e));
        dont_printf("    %s\n", type_show(ty, t0));
        //printf("SolveCall(%s, %s) = %s\n", show_expr(e), type_show(ty, t0), type_show(ty, t));
        return t0;
}

static Expr *
FindMethod_(expression_vector const *ms, char const *name)
{
        for (int i = 0; i < vN(*ms); ++i) {
                if (strcmp(name, v__(*ms, i)->name) == 0) {
                        return v__(*ms, i);
                }
        }

        return NULL;
}

static Expr *
FindMethod(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethod_(&c->def->class.methods, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindMethod(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

static Expr *
FindStatic(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethod_(&c->def->class.statics, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindStatic(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

static Expr *
FindField_(expression_vector const *fs, char const *name)
{
        for (int i = 0; i < vN(*fs); ++i) {
                Expr *field = v__(*fs, i);
                if (strcmp(FieldIdentifier(field)->identifier, name) == 0) {
                        return field;
                }
        }

        return NULL;
}

static Expr *
FindField(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindField_(&c->def->class.fields, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindField(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

Type *
SolveMemberAccess(Ty *ty, Type *t0, Type *t1)
{
        Type *t;
        Symbol *var;

        for (int i = 0; i < vN(t0->args) && i < vN(t0->class->type->params); ++i) {
                var = scope_insert(
                        ty,
                        ty->tscope,
                        v__(t0->class->type->params, i)
                );
                var->type = v__(t0->args, i);
                dont_printf("SolveMemberAccess(): %s := %s  (args=%zu, params=%zu)\n", var->identifier, type_show(ty, var->type), vN(t0->args), vN(t0->params));
        }

        t = Propagate(ty, t1);
        dont_printf("SolveMemberAccess(%s): %s\n", type_show(ty, t1), type_show(ty, t));

        return t;
}

Type *
type_member_access_t(Ty *ty, Type *t0, char const *name)
{
        dont_printf("member_access(%s, %s)\n", type_show(ty, t0), name);

        if (NullOrAny(t0)) {
                return ANY;
        }

        if (IsNil(t0)) {
                return NIL;
        }

        Type *t1;
        int class;
        Class *c;
        Value *field;
        Expr *f;
        Symbol *var;

        switch (t0->type) {
        case TYPE_UNION:
                t1 = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify(ty, &t1, type_member_access_t(ty, v__(t0->types, i), name));
                }
                return t1;

        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        char const *e_name = v__(t0->names, i);
                        if (
                                e_name == name
                             || (
                                     e_name != NULL
                                  && name   != NULL
                                  && strcmp(e_name, name) == 0
                                )
                        ) {
                                return v__(t0->types, i);
                        }
                }
                return NULL;

        case TYPE_OBJECT:
                class = ClassOfType(ty, t0);
                field = (class >= CLASS_PRIMITIVE)
                      ? class_lookup_field_i(ty, class, M_ID(name))
                      : NULL;
                if (field != NULL) {
                        return SolveMemberAccess(
                                ty,
                                t0,
                                (
                                        (field->extra != NULL)
                                      ? type_resolve(ty, field->extra)
                                      : ((Expr *)field->ptr)->_type
                                )
                        );
                }

                c = class_get_class(ty, class);

                f = FindMethod(c, name);
                if (f != NULL) {
                        return SolveMemberAccess(ty, t0, f->_type);
                }
                return NULL;

        case TYPE_VARIABLE:
                dont_printf("Ok based\n");
                t1 = NewType(ty, TYPE_TUPLE);
                avP(t1->names, name);
                avP(t1->types, GenScopedVar(ty));
                var = scope_find_symbol(ty->tscope, t0->var);
                if (var == NULL || var->type == t0) {
                        var = scope_insert(
                                ty,
                                (t0->var->scope == NULL) ? FunTypeScope(ty) : ty->tscope,
                                t0->var
                        );
                        var->type = t1;
                        dont_printf("(1) %s := %s\n", t0->var->identifier, type_show(ty, t0->var->type));
                        dont_printf("(2) %s := %s\n", var->identifier, type_show(ty, var->type));
                } else {
                        type_intersect(ty, &var->type, t1);
                }
                return *vvL(t1->types);
        }

        return NULL;
}

Type *
type_member_access(Ty *ty, Expr const *e)
{
        ty->tscope = scope_new(ty, "", ty->tscope, false);

        Type *t0 = e->type == EXPRESSION_DYN_MEMBER_ACCESS
                 ? UnionOf(ty, e->object->_type)
                 : type_member_access_t(ty, e->object->_type, e->member_name);

        ty->tscope = ty->tscope->parent;

        return t0;
}

Type *
type_method_call_t(Ty *ty, Expr const *e, Type *t0, char const *name)
{
        if (IsNil(t0)) {
                return NIL;
        }

        if (NullOrAny(t0) || e->type == EXPRESSION_DYN_METHOD_CALL) {
                return ANY;
        }

        Class *c;
        Expr *f;
        Type *t;

        switch (t0->type) {
        case TYPE_OBJECT:
        case TYPE_VARIABLE:
        case TYPE_TUPLE:
                t = Propagate(ty, type_member_access_t(ty, t0, name));
                t = type_call_t(ty, e, t);
                return t;
        
        case TYPE_CLASS:
                c = t0->class;
                f = FindStatic(c, name);
                return ReturnType(f);

        case TYPE_UNION:
                t = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify(ty, &t, type_method_call_t(ty, e, v__(t0->types, i), name));
                }
                return t;
        }

        return NULL;
}

Type *
type_method_call_name(Ty *ty, Type *t0, char const *name)
{
        ty->tscope = scope_new(ty, "", ty->tscope, false);

        Type *t1 = type_method_call_t(ty, &(Expr){ .type = EXPRESSION_METHOD_CALL }, t0, name);
        dont_printf("type_method_call_name()\n");
        dont_printf("    %s\n", name);
        dont_printf("    %s\n", type_show(ty, t0));
        dont_printf("    %s\n", type_show(ty, t1));

        ty->tscope = ty->tscope->parent;

        return t1;
}

Type *
type_method_call(Ty *ty, Expr const *e)
{
        ty->tscope = scope_new(ty, "", ty->tscope, false);

        Type *t0 = type_method_call_t(ty, e, e->object->_type, e->method_name);
        dont_printf("type_method_call()\n");
        dont_printf("    >>> %s\n", show_expr(e));
        dont_printf("    %s\n", type_show(ty, e->object->_type));
        dont_printf("    %s\n", type_show(ty, t0));

        ty->tscope = ty->tscope->parent;

        return t0;
}

Type *
type_subscript_t(Ty *ty, Type *t0, Type *t1)
{
        Type *t = ANY;
        Type *t2;

        if (t0 == NULL) {
                return NULL;
        }

        switch (t0->type) {
        case TYPE_OBJECT:
                switch (t0->class->i) {
                case CLASS_ARRAY: t = Propagate(ty, TypeArg(t0, 0)); break;
                case CLASS_DICT:  t = TypeArg(t0, 1);                break;
                }
                break;

        case TYPE_UNION:
                t2 = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify(ty, &t2, type_subscript_t(ty, v__(t0->types, i), t1));
                }
                t = t2;
                break;

        case TYPE_TUPLE:
                t = (t1->type == TYPE_INTEGER)
                     ? RecordElem(t0, t1->z)
                     : UnionOf(ty, t0);
                break;
        }

        dont_printf("subscript(%s): %s\n", type_show(ty, t0), type_show(ty, t));

        return t;
}

Type *
type_subscript(Ty *ty, Expr const *e)
{
        return type_subscript_t(ty, e->container->_type, e->subscript->_type);
}

static bool
check_entry(Ty *ty, Type *t0, int i, Type *t1, bool bind)
{
        if (NullOrAny(t0)) {
                return false;
        }

        switch (t0->type) {
        case TYPE_UNION:
                for (int ii = 0; ii < vN(t0->types); ++ii) {
                        if (!check_entry(ty, v__(t0->types, ii), i, t1, bind)) {
                                return false;
                        }
                }
                return true;

        case TYPE_TUPLE:
                return vN(t0->types) > i
                    && type_check_x(ty, v__(t0->types, i), t1, bind);
        }

        return false;
}

static bool
check_field(Ty *ty, Type *t0, char const *name, Type *t1, bool bind)
{
        if (NullOrAny(t0)) {
                return false;
        }

        Value const *field;

        switch (t0->type) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!check_field(ty, v__(t0->types, i), name, t1, bind)) {
                                return false;
                        }
                }
                return true;

        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        char const *e_name = v__(t0->names, i);
                        if (
                                e_name == name
                             || (
                                     e_name != NULL
                                  && name   != NULL
                                  && strcmp(e_name, name) == 0
                                )
                        ) {
                                return type_check_x(ty, v__(t0->types, i), t1, bind);
                        }
                }
                return false;

        case TYPE_OBJECT:
                field = class_lookup_field_i(ty, t0->class->i, M_ID(name));
                if (field != NULL) {
                        return type_check_x(
                                ty,
                                (
                                        (field->extra != NULL)
                                      ? type_resolve(ty, field->extra)
                                      : ((Expr *)field->ptr)->_type
                                ),
                                t1,
                                bind
                        );
                }
        }

        return false;
}

static int d = 0;
//#define print(fmt, ...) dont_printf("%*s" fmt "\n", d*4, "", __VA_ARGS__ + 0)
#define print(...) 0

bool
type_check_x_(Ty *ty, Type *t0, Type *t1, bool bind)
{
        if (NullOrAny(t0) || t0 == t1) {
                return true;
        }

        if (t1 == NULL) {
                return false;
        }

        if (
                t0->type == TYPE_OBJECT
             && t0->class->i == CLASS_CLASS
             && t1->type == TYPE_CLASS
        ) {
                return true;
        }

        if (t0->type == TYPE_VARIABLE) {
                Symbol *var = scope_find_symbol(ty->tscope, t0->var);
                if (var != NULL) {
                        Type *t0_ = (var == NULL) ? NULL : var->type;
                        if (t0_ == NULL || t0_ == t0->var->type || t0_ == t0) {
                                if (!bind) {
                                        return true;
                                }
                                Symbol *var = scope_insert(ty, ty->tscope, t0->var);
                                var->type = CloneType(ty, t1);
                                if (var->type != NULL) {
                                        v0(var->type->args);
                                }
                                var->type = Relax(Propagate(ty, var->type));
                                return true;
                        }
                        if (vN(t0_->args) != ArgCount(t1)) {
                                return false;
                        }
                        for (int i = 0; i < vN(t0->args); ++i) {
                                if (
                                        !type_check(
                                                ty, 
                                                v__(t0_->args, i),
                                                TypeArg(t1, i)
                                        )
                                ) {
                                        return false;
                                }
                        }
                        return type_check_x(ty, t0_, t1, bind);
                }
        }

        if (t1->type == TYPE_VARIABLE) {
                Symbol *var = scope_find_symbol(ty->tscope, t1->var);
                if (var == NULL) {
                        return false;
                }
                Type *t1_ = (var == NULL) ? NULL : var->type;
                if (t1_ == NULL || t1_ == t1->var->type || t1_ == t1) {
                        if (!bind) {
                                return true;
                        }
                        Symbol *var = scope_insert(ty, ty->tscope, t1->var);
                        var->type = CloneType(ty, t0);
                        if (var->type != NULL) {
                                v0(var->type->args);
                        }
                        var->type = Relax(Propagate(ty, var->type));
                        return true;
                }
                if (vN(t1_->args) != ArgCount(t0)) {
                        return false;
                }
                for (int i = 0; i < vN(t1->args); ++i) {
                        if (
                                !type_check(
                                        ty, 
                                        v__(t1_->args, i),
                                        TypeArg(t0, i)
                                )
                        ) {
                                return false;
                        }
                }
                return type_check_x(ty, t1_, t0, bind);
        }

        if (t0->type == TYPE_UNION && t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (!type_check_x(ty, t0, v__(t1->types, i), bind)) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_INTEGER && t1->type == TYPE_INTEGER) {
                return t0->z == t1->z;
        }

        if (t0->type == TYPE_UNION) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (type_check_x(ty, v__(t0->types, i), t1, bind)) {
                                return true;
                        }
                }
                return false;
        }

        if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (!type_check_x(ty, t0, v__(t1->types, i), bind)) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_OBJECT) {
                int c0 = t0->class->i;
                int c1 = ClassOfType(ty, t1);
                if (
                        c0 != c1
                     && c0 > CLASS_OBJECT
                     && (
                                c0 < CLASS_PRIMITIVE
                             || c1 < CLASS_PRIMITIVE
                             || !class_is_subclass(ty, c1, c0)
                        )
                ) {
                        return false;
                }
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (
                                !type_check_x(
                                        ty,
                                        v__(t0->args, i),
                                        TypeArg(t1, i),
                                        bind
                                )
                        ) {
                                return false;
                        }
                }
                return true;
        }

        if (t1->type == TYPE_TUPLE) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        char const *name = v__(t1->names, i);
                        if (
                                name == NULL
                              ? !check_entry(ty, t0, i, v__(t1->types, i), bind)
                              : !check_field(ty, t0, name, v__(t1->types, i), bind)
                        ) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_FUNCTION && t1->type == TYPE_FUNCTION) {
                for (int i = 0; i < max(vN(t0->fun_params), vN(t1->fun_params)); ++i) {
                        Type *a0 = (vN(t0->fun_params) > i)
                                 ? v_(t0->fun_params, i)->type
                                 : NIL_TYPE;
                        Type *a1 = (vN(t1->fun_params) > i)
                                 ? v_(t1->fun_params, i)->type
                                 : NIL_TYPE;
                        if (!type_check_x(ty, a1, a0, bind)) {
                                return false;
                        }
                }
                return type_check_x(ty, t0->rt, t1->rt, bind);
        }

        return false;
}

bool type_check_x(Ty *ty, Type *t0, Type *t1, bool bind)
{
        static int d = 0;
        dont_printf("%*stype_check():\n", 4*d, "");
        dont_printf("%*s    %s\n", 4*d, "", type_show(ty, t0));
        dont_printf("%*s    %s\n", 4*d, "", type_show(ty, t1));
        d += 1;
        bool b = type_check_x_(ty, t0, t1, bind);
        d -= 1;
        dont_printf("%*s => %s\n", 4*d, "", b ? "true" : "false");
        return b;
}


bool
type_check(Ty *ty, Type *t0, Type *t1)
{
        d += 1;
        //ty->tscope = scope_new(ty, "", ty->tscope, true);
        bool b = type_check_x(ty, t0, t1, true);
        //ty->tscope = ty->tscope->parent;
        d -= 1;
        return b;
}

Type *
type_tuple(Ty *ty, Expr const *e)
{
        Type *t0 = NewType(ty, TYPE_TUPLE);

        for (int i = 0; i < vN(e->es); ++i) {
                avP(t0->types, Relax(v__(e->es, i)->_type));
                avP(t0->names, v__(e->names, i));
        }

        return t0;
}

Type *
type_dict(Ty *ty, Expr const *e)
{
        Type *t0 = NULL;
        Type *t1 = NULL;

        for (int i = 0; i < vN(e->keys); ++i) {
                unify(ty, &t0, v__(e->keys, i)->_type);
                unify(
                        ty,
                        &t1,
                        (v__(e->values, i) == NULL) ? NIL : v__(e->values, i)->_type
                );
        }

        Type *t = type_object(ty, class_get_class(ty, CLASS_DICT));
        avP(t->args, Relax(t0));
        avP(t->args, Relax(t1));

        return t;
}

static Type *
ArrayOf(Ty *ty, Type *t0)
{
        Type *t = CloneType(ty, TYPE_ARRAY);
        CloneVec(t->args);
        v0(t->args);
        avP(t->args, t0);
        return t;
}

Type *
type_array(Ty *ty, Expr const *e)
{
        Type *t0 = NULL;

        for (int i = 0; i < vN(e->elements); ++i) {
                unify(ty, &t0, v__(e->elements, i)->_type);
        }

        return ArrayOf(ty, Relax(t0));
}

void
type_assign(Ty *ty, Expr *e, Type *t0)
{
        if (t0 == NULL) {
                t0 = TYPE_ANY;
        }

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_RESOURCE_BINDING:
                unify(ty, &e->_type, t0);
                unify(ty, &e->symbol->type, t0);
                dont_printf("type(%s) := %s  ==>  %s\n", e->symbol->identifier, type_show(ty, t0), type_show(ty, e->symbol->type));
                break;
        case EXPRESSION_TAG_APPLICATION:
                for (int i = 0; i < UnionCount(t0); ++i) {
                        Type *t1 = UnionElem(t0, i);
                        dont_printf("type_assign(): t1 = %s\n", type_show(ty, t1));
                        if (IsTagged(t1) && TagOf(t1) == e->symbol->tag) {
                                dont_printf("type_assign(): %s |= %s\n", type_show(ty, e->tagged->_type), type_show(ty, t1));
                                type_assign(ty, e->tagged, TypeArg(t1, 0));
                        }
                }
                break;
        case EXPRESSION_ARRAY:
                switch (ClassOfType(ty, t0)) {
                case CLASS_ARRAY:
                        for (int i = 0; i < vN(e->elements); ++i) {
                                type_assign(
                                        ty,
                                        v__(e->elements, i),
                                        type_subscript_t(ty, t0, TYPE_INT)
                                );
                        }
                }
                break;
        case EXPRESSION_TUPLE:
                switch (t0->type) {
                case TYPE_TUPLE:
                        for (int i = 0; i < vN(e->es); ++i) {
                                type_assign(
                                        ty,
                                        v__(e->es, i),
                                        vN(t0->types) > i ? v__(t0->types, i) : ANY
                                );
                        }
                }
                break;
        case EXPRESSION_LIST:
                type_assign(ty, v__(e->es, 0), t0);
                break;
        }
}

Type *
type_resolve(Ty *ty, Expr const *e)
{
        Type *t0;
        Symbol *var;

        if (e == NULL) {
                return NULL;
        }

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (e->symbol->class != -1) {
                        t0 = class_get_class(ty, e->symbol->class)->object_type;
                } else if (e->symbol->tag != -1) {
                        t0 = e->symbol->type;
                } else {
                        var = scope_find_symbol(ty->tscope, e->symbol);
                        if (var != NULL) {
                                t0 = var->type;
                                if (t0->type == TYPE_ALIAS && vN(t0->args) == vN(t0->params)) {
                                        t0 = ResolveAlias(ty, t0);
                                }
                        } else if (e->symbol->type_var) {
                                t0 = e->symbol->type;
                        } else {
                                t0 = NULL;
                        }
                }
                dont_printf("resolve(): %s -> %s\n", e->identifier, type_show(ty, t0));
                return t0;

        case EXPRESSION_TYPEOF:
                return e->operand->_type;

        case EXPRESSION_TYPE:
                return e->_type;

        case EXPRESSION_SUBSCRIPT:
                t0 = CloneType(ty, type_resolve(ty, e->container));
                if (t0 != NULL) {
                        CloneVec(t0->args);
                        avP(t0->args, type_resolve(ty, e->subscript));
                        if (t0->type == TYPE_TAG) {
                                t0->type = TYPE_OBJECT;
                        }
                }
                dont_printf("resolve_subscript(): -> %s\n", type_show(ty, t0));
                return Propagate(ty, t0);

        case EXPRESSION_TUPLE:
                t0 = NewType(ty, TYPE_TUPLE);
                for (int i = 0; i < vN(e->es); ++i) {
                        avP(t0->names, v__(e->names, i));
                        avP(t0->types, type_resolve(ty, v__(e->es, i)));
                }
                return t0;

        case EXPRESSION_BIT_OR:
                t0 = NULL;
                unify(ty, &t0, type_resolve(ty, e->left));
                unify(ty, &t0, type_resolve(ty, e->right));
                return t0;

        case EXPRESSION_FUNCTION:
                t0 = NewType(ty, TYPE_FUNCTION);
                t0->rt = type_resolve(ty, v__(e->body->returns, 0));
                return t0;

        case EXPRESSION_FUNCTION_TYPE:
                t0 = NewType(ty, TYPE_FUNCTION);
                if (e->left->type == EXPRESSION_LIST) {
                        Symbol *name = amA0(sizeof *name);
                        name->identifier = "_";
                        for (int i = 0; i < vN(e->left->es); ++i) {
                                avP(
                                        t0->fun_params,
                                        PARAM(
                                                name,
                                                type_resolve(
                                                        ty,
                                                        v__(e->left->es, i)
                                                )
                                        )
                                );
                        }
                } else if (e->left->type == EXPRESSION_TUPLE) {
                        for (int i = 0; i < vN(e->left->es); ++i) {
                                Symbol *name = amA0(sizeof *name);
                                name->identifier = vN(e->left->names) > i
                                                 ? v__(e->left->names, i)
                                                 : "_";
                                avP(
                                        t0->fun_params,
                                        PARAM(
                                                name,
                                                type_resolve(
                                                        ty,
                                                        v__(e->left->es, i)
                                                )
                                        )
                                );
                        }
                } else {
                        Symbol *name = amA0(sizeof *name);
                        name->identifier = "_";
                        avP(t0->fun_params, PARAM(name, type_resolve(ty, e->left)));
                }
                t0->rt = type_resolve(ty, e->right);
                return t0;

        case EXPRESSION_ARRAY:
                t0 = (vN(e->elements) == 0) ? NULL : type_resolve(
                        ty,
                        v__(e->elements, 0)
                );
                return ArrayOf(ty, t0);

        case EXPRESSION_NIL:
                return NIL;
        }

        dont_printf("resolve() failed: %s\n", show_expr(e));

        return NULL;
}

static bool
try_coalesce(Ty *ty, Type **t0, Type *t1)
{
        if (*t0 == NULL || t1 == NULL) {
                return false;
        }

        if (
                IsTagged(*t0)
             && IsTagged(t1)
             && TagOf(*t0) == TagOf(t1)
        ) {
                unify(ty, t0, t1);
                return true;
        }

        if (
                (*t0)->type == TYPE_INTEGER
             && t1->type == TYPE_INTEGER
        ) {
                *t0 = TYPE_INT;
                return true;
        }

        return false;
}

void
unify_(Ty *ty, Type **t0, Type *t1)
{
        if (*t0 == NULL) {
                *t0 = t1;
                return;
        }

        if ((*t0)->fixed) {
                return;
        }

        if (NullOrAny(t1)) {
                *t0 = ANY;
                return;

        }

        if (type_check(ty, *t0, t1)) {
                return;
        }

        if (t1->type == TYPE_INTEGER) {
                for (int i = 0; i < UnionCount(*t0); ++i) {
                        Type **t2 = UnionElemPtr(t0, i);
                        if ((*t2)->type == TYPE_INTEGER) {
                                if (t1->z != (*t2)->z) {
                                        *t2 = TYPE_INT;
                                }
                                return;
                        }
                }
        }

        if (
                IsTagged(*t0)
             && IsTagged(t1)
             && (*t0)->class == t1->class
        ) {
                unify(ty, v_((*t0)->args, 0), v__(t1->args, 0));
        } else if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        unify(ty, t0, v__(t1->types, i));
                }
        } else if ((*t0)->type == TYPE_UNION) {
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        if (try_coalesce(ty, v_((*t0)->types, i), t1)) {
                                return;
                        }
                }
                avP((*t0)->types, t1);
        } else {
                Type *union_ = NewType(ty, TYPE_UNION);
                avP(union_->types, *t0);
                avP(union_->types, t1);
                *t0 = union_;
        }
}

void
unify(Ty *ty, Type **t0, Type *t1)
{
        static int d = 0;
        //char const *s0 = type_show(ty, *t0);
        //char const *s1 = type_show(ty, t1);
        //printf("%*sunify(%s, %s)\n", d*4, "", s0, s1);
        d += 1;
        unify_(ty, t0, t1);
        d -= 1;
        //printf("%*sunify(%s, %s)  =>  %s\n", d*4, "", s0, s1, type_show(ty, *t0));
}

inline static bool
is_record(Type const *t0)
{
        if (t0->type != TYPE_TUPLE) {
                return false;
        }

        for (int i = 0; i < vN(t0->types); ++i) {
                if (v__(t0->names, i) != NULL) {
                        return true;
                }
        }

        return false;
}

char *
type_show(Ty *ty, Type *t0)
{
        static int dt = 0;

        dt += 1;

        if (dt > 20) { *(char *)0 = 0; }

        if (NullOrAny(t0)) {
                dt -= 1;
                return sclone_malloc("Any");
        }

        Symbol *var;
        byte_vector buf = {0};

        switch (t0->type) {
        case TYPE_OBJECT:
                switch (t0->class->i) {
                case CLASS_INT:     dump(&buf, "Int");    break;
                case CLASS_FLOAT:   dump(&buf, "Float");  break;
                case CLASS_STRING:  dump(&buf, "String"); break;
                case CLASS_BOOL:    dump(&buf, "Bool");   break;
                case CLASS_BLOB:    dump(&buf, "Blob");   break;
                case CLASS_ARRAY:   dump(&buf, "Array");  break;
                case CLASS_DICT:    dump(&buf, "Dict");   break;
                case CLASS_NIL:     dump(&buf, "nil");    break;
                default:            dump(&buf, "%s",  t0->class->name); break;
                }
                if (vN(t0->args) > 0) {
                        dump(&buf, "[");
                        for (int i = 0; i < vN(t0->args); ++i) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        type_show(ty, v__(t0->args, i))
                                );
                        }
                        dump(&buf, "]");
                }
                break;
        case TYPE_CLASS:
                dump(&buf, "Class[%s]", t0->class->name);
                break;
        case TYPE_TAG:
                dump(&buf, "Tag[%s]", t0->class->name);
                break;
        case TYPE_TYPE:
                dump(&buf, "Type[%s]", type_show(ty, t0->_type));
                break;
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        dump(
                                &buf,
                                (i == 0) ? "%s" : " | %s",
                                type_show(ty, v__(t0->types, i))
                        );

                }
                break;
        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        dump(
                                &buf,
                                (i == 0) ? "%s" : " & %s",
                                type_show(ty, v__(t0->types, i))
                        );

                }
                break;
        case TYPE_FUNCTION:
                if (vN(t0->params) > 0) {
                        dump(&buf, "[");
                        for (int i = 0; i < vN(t0->params); ++i) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        v__(t0->params, i)->identifier
                                );
                        }
                        dump(&buf, "]");
                }
                if (vN(t0->constraints) > 0) {
                        for (int i = 0; i < vN(t0->constraints); ++i) {
                                Constraint *c = v_(t0->constraints, i);
                                switch (c->type) {
                                case TC_2OP:
                                        dump(
                                                &buf,
                                                "(%s %s %s -> %s)",
                                                type_show(ty, c->t0),
                                                intern_entry(&xD.b_ops, c->op)->name,
                                                type_show(ty, c->t1),
                                                type_show(ty, c->rt)
                                        );
                                        break;
                                }
                        }
                        dump(&buf, " => ");
                }
                dump(&buf, "(");
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (p->var == NULL) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        type_show(ty, p->type)
                                );
                        } else {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s: %s" : ", %s: %s",
                                        p->var->identifier,
                                        type_show(ty, p->type)
                                );
                        }
        
                }
                dump(&buf, ")");
                dump(&buf, " -> %s", type_show(ty, t0->rt));
                break;
        case TYPE_TUPLE:
                if (is_record(t0)) {
                        dump(&buf, "{");
                        for (int i = 0; i < vN(t0->types); ++i) {
                                if (v__(t0->names, i) == NULL) {
                                        dump(
                                                &buf,
                                                (i == 0) ? "%d: %s" : ", %d: %s",
                                                i,
                                                type_show(ty, v__(t0->types, i))
                                        );
                                } else {
                                        dump(
                                                &buf,
                                                (i == 0) ? "%s: %s" : ", %s: %s",
                                                v__(t0->names, i),
                                                type_show(ty, v__(t0->types, i))
                                        );
                                }
                        }
                        dump(&buf, "}");
                } else {
                        dump(&buf, "(");
                        for (int i = 0; i < vN(t0->types); ++i) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        type_show(ty, v__(t0->types, i))
                                );
                        }
                        dump(&buf, ")");
                }
                break;

        case TYPE_VARIABLE:
                var = scope_find_symbol(ty->tscope, t0->var);
                if (t0->mark || var == NULL || var->type == t0 || var == t0->var) {
                        dump(&buf, "%s", t0->var->identifier);
                } else {
                        t0->mark = true;
                        dump(&buf, "%s=%s", t0->var->identifier, type_show(ty, var->type));
                        t0->mark = false;
                }
                if (vN(t0->args) > 0) {
                        dump(&buf, "[");
                        for (int i = 0; i < vN(t0->args); ++i) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        type_show(ty, v__(t0->args, i))
                                );
                        }
                        dump(&buf, "]");
                }
                break;

        case TYPE_ALIAS:
                if (vN(t0->params) > 1) {
                        dump(&buf, "(%s", v__(t0->params, 0)->identifier);
                        for (int i = 1; i < vN(t0->params); ++i) {
                                dump(&buf, ", %s", v__(t0->params, i)->identifier);
                        }
                        dump(&buf, ") -> ");
                } else if (vN(t0->params) == 1) {
                        dump(&buf, "%s -> ", v__(t0->params, 0)->identifier);
                }
                dump(&buf, "%s", type_show(ty, t0->_type));
                break;

        case TYPE_NIL:
                dt -= 1;
                return sclone_malloc("nil");

        case TYPE_INTEGER:
                dump(&buf, "%"PRIiMAX, t0->z);
                break;
        }

        dt -= 1;

        return vN(buf) == 0 ? sclone_malloc("<?>") : buf.items;
}

Type *
type_fixed(Ty *ty, Type *t0)
{
        Type *t;

        if (t0 != NULL) {
                t = CloneType(ty, t0);
                t->fixed = true;
        } else {
                t = NULL;
        }

        return t;
}

Expr *
type_find_member(Ty *ty, Type *t0, char const *name)
{
        if (t0 == NULL) {
                return NULL;
        }

        Expr *m = NULL;

        switch (t0->type) {
        case TYPE_OBJECT:
                m = FindMethod(t0->class, name);
                if (m == NULL) {
                        m = FieldIdentifier(FindField(t0->class, name));
                }
                break;

        case TYPE_CLASS:
                m = FindStatic(t0->class, name);
                break;
        }

        return m;
}

static Type *
TypeOf2Op(Ty *ty, int op, Type *t0, Type *t1)
{
        if (op == -1) {
                return NULL;
        }

        if (t0 == NULL) {
                t0 = ANY;
        }

        if (t1 == NULL) {
                t1 = ANY;
        }


        if (t0 != NULL && t0->type == TYPE_UNION) {
                Type *t = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify(
                                ty,
                                &t,
                                TypeOf2Op(
                                        ty,
                                        op,
                                        v__(t0->types, i),
                                        t1
                                )
                        );
                }
                return t;
        }

        if (t1 != NULL && t1->type == TYPE_UNION) {
                Type *t = NULL;
                for (int i = 0; i < vN(t1->types); ++i) {
                        unify(
                                ty,
                                &t,
                                TypeOf2Op(
                                        ty,
                                        op,
                                        t0,
                                        v__(t1->types, i)
                                )
                        );
                }
                return t;
        }

        if (
                t0->type == TYPE_INTEGER
             && t1->type == TYPE_INTEGER
        ) {
                switch (op) {
                case OP_ADD: return type_integer(ty, t0->z + t1->z);
                case OP_SUB: return type_integer(ty, t0->z - t1->z);
                case OP_MUL: return type_integer(ty, t0->z * t1->z);
                case OP_DIV: return type_integer(ty, t0->z / t1->z);
                case OP_MOD: return type_integer(ty, t0->z % t1->z);
                }
        }

        uint32_t c0 = ClassOfType(ty, t0);
        uint32_t c1 = ClassOfType(ty, t1);
        Expr *fun = op_fun_info(op, c0, c1);

        if (fun == NULL) {
                switch (op) {
                case OP_ADD:
                        switch (PACK_TYPES(c0, c1)) {
                        case PAIR_OF(CLASS_INT):                 return TYPE_INT;
                        case PAIR_OF(CLASS_FLOAT):               return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_INT, CLASS_FLOAT): return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_FLOAT, CLASS_INT): return TYPE_FLOAT;
                        case PAIR_OF(CLASS_ARRAY):               return t0;
                        case PAIR_OF(CLASS_STRING):              return t0;
                        case PAIR_OF(CLASS_DICT):                return t0;
                        default:
                                return NULL;
                        }

                case OP_SUB:
                        switch (PACK_TYPES(c0, c1)) {
                        case PAIR_OF(CLASS_INT):                 return TYPE_INT;
                        case PAIR_OF(CLASS_FLOAT):               return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_INT, CLASS_FLOAT): return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_FLOAT, CLASS_INT): return TYPE_FLOAT;
                        case PAIR_OF(CLASS_ARRAY):               return t0;
                        case PAIR_OF(CLASS_STRING):              return t0;
                        case PAIR_OF(CLASS_DICT):                return t0;
                        default:
                                return NULL;
                        }

                case OP_MUL:
                        switch (PACK_TYPES(c0, c1)) {
                        case PAIR_OF(CLASS_INT):                 return TYPE_INT;
                        case PAIR_OF(CLASS_FLOAT):               return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_INT, CLASS_FLOAT): return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_FLOAT, CLASS_INT): return TYPE_FLOAT;
                        case PAIR_OF(CLASS_ARRAY):               return t0;
                        case PAIR_OF(CLASS_STRING):              return t0;
                        case PAIR_OF(CLASS_DICT):                return t0;
                        default:
                                return NULL;
                        }

                case OP_DIV:
                        switch (PACK_TYPES(c0, c1)) {
                        case PAIR_OF(CLASS_INT):                 return TYPE_INT;
                        case PAIR_OF(CLASS_FLOAT):               return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_INT, CLASS_FLOAT): return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_FLOAT, CLASS_INT): return TYPE_FLOAT;
                        case PAIR_OF(CLASS_ARRAY):               return t0;
                        case PAIR_OF(CLASS_DICT):                return t0;
                        default:
                                return NULL;
                        }

                case OP_MOD:
                        switch (PACK_TYPES(c0, c1)) {
                        case PAIR_OF(CLASS_INT):                 return TYPE_INT;
                        case PAIR_OF(CLASS_FLOAT):               return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_INT, CLASS_FLOAT): return TYPE_FLOAT;
                        case PACK_TYPES(CLASS_FLOAT, CLASS_INT): return TYPE_FLOAT;
                        case PAIR_OF(CLASS_ARRAY):               return t0;
                        case PAIR_OF(CLASS_DICT):                return t0;
                        default:
                                return NULL;
                        }
                }

                return NULL;
        }

        Expr arg1 = { ._type = t0 };
        Expr arg2 = { ._type = t1 };
        Expr *argv[] = { &arg1, &arg2 };

        Expr call = {
                .type = EXPRESSION_FUNCTION_CALL,
                .args = { .items = argv, .count = 2 },
                .function = fun
        };

        Type *t = (fun == NULL) ? NULL : type_call_t(ty, &call, fun->_type);

        dont_printf(
                "TypeOf2Op(%s):\n  %s\n  %s\n => %s\n",
                intern_entry(&xD.b_ops, op)->name,
                type_show(ty, t0),
                type_show(ty, t1),
                type_show(ty, t)
        );

        return t;
}

Type *
type_binary_op(Ty *ty, Expr const *e)
{
        Type *t0 = e->left->_type;
        Type *t1 = e->right->_type;

        if (t0 == NULL || t1 == NULL) {
                return NULL;
        }

        int op = -1;

        switch (e->type) {
        case EXPRESSION_PLUS:    op = OP_ADD; break;
        case EXPRESSION_MINUS:   op = OP_SUB; break;
        case EXPRESSION_DIV:     op = OP_DIV; break;
        case EXPRESSION_STAR:    op = OP_MUL; break;
        case EXPRESSION_PERCENT: op = OP_MOD; break;
        case EXPRESSION_USER_OP: op = intern(&xD.b_ops, e->op_name)->id;
        }

        if (op == -1) {
                return NULL;
        }

        if (t0->type == TYPE_VARIABLE || t1->type == TYPE_VARIABLE) {
                Type *ft = TyCompilerState(ty)->func->_type;
                Type *t2 = GenVar(ty);
                avP(
                        ft->constraints,
                        ((Constraint){
                                .type = TC_2OP,
                                .t0 = t0,
                                .t1 = t1,
                                .rt = t2,
                                .op = op
                        })
                );
                return t2;
        }

        return TypeOf2Op(ty, op, t0, t1);
}

Type *
type_array_of(Ty *ty, Type *t0)
{
        return ArrayOf(ty, t0);
}

Type *
type_iterable_type(Ty *ty, Type *t0)
{
        if (ClassOfType(ty, t0) == CLASS_ARRAY) {
                return TypeArg(t0, 0);
        }

        return NULL;
}

void
type_scope_push(Ty *ty, bool fun)
{
        ty->tscope = scope_new(ty, "", ty->tscope, fun);
}

void
type_scope_pop(Ty *ty)
{
        ty->tscope = ty->tscope->parent;
}

void
type_function_fixup(Ty *ty, Type *t)
{
        if (t == NULL) {
                return;
        }

        for (int i = 0; i < IntersectCount(t); ++i) {
                Type *t0 = IntersectElem(t, i);

                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param *p = v_(t0->fun_params, i);
                        p->type = Propagate(ty, p->type);
                }

                int n = 0;
                for (int i = 0; i < vN(t0->params); ++i) {
                        Symbol *p = v__(t0->params, i);
                        Type *p0 = Propagate(ty, p->type);
                        dont_printf("%s :: %s :: %s\n", p->identifier, type_show(ty, p->type), type_show(ty, p0));
                        if (p->type == p0) {
                                dont_printf("Keep %s :: %d\n", p->identifier, n);
                                *v_(t0->params, n) = p;
                                n += 1;
                        } else {
                                dont_printf("Discard %s\n", p->identifier);
                                scope_insert(ty, GlobalTypeScope(ty), p)->type = p0;
                        }
                }

                t0->params.count = n;
        }
}

void
type_intersect(Ty *ty, Type **t0, Type *t1)
{
        dont_printf("intersect()\n");
        dont_printf("    %s\n", type_show(ty, *t0));
        dont_printf("    %s\n", type_show(ty, t1));

        if (*t0 == NULL) {
                *t0 = t1;
                return;
        }

        if (t1 == NULL) {
                return;
        }

        if ((*t0)->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        if (type_check(ty, t1, v__((*t0)->types, i))) {
                                return;
                        }
                }
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        if (type_check(ty, v__((*t0)->types, i), t1)) {
                                *v_((*t0)->types, i) = t1;
                                return;
                        }
                }
                avP((*t0)->types, t1);
                return;
        }

        Type *t2 = NewType(ty, TYPE_INTERSECT);
        avP(t2->types, *t0);
        avP(t2->types, t1);
        *t0 = t2;
}

bool
TypeCheck(Ty *ty, Type *t0, Value const *v)
{
        dont_printf("TypeCheck():\n");
        dont_printf("    %s\n", VSC(v));
        dont_printf("    %s\n", type_show(ty, t0));

        Value *var;

        if (NullOrAny(t0)) {
                return true;
        }

        if (v->type == VALUE_NIL) {
                return type_check_x(ty, t0, NIL_TYPE, false);
        }

        switch (t0->type) {
        case TYPE_INTEGER:
                return v->type == VALUE_INTEGER
                    && v->integer == t0->z;

        /*
         *
         * fn foo[T](xs: Array[T]) {
         * }
         *
         */
        case TYPE_VARIABLE:
                var = vm_local(ty, t0->var->i);
                if (var->type == VALUE_NIL) {
                        *var = TYPE(class_get_class(ty, ClassOf(v))->object_type);
                        return true;
                } else {
                        return TypeCheck(ty, var->ptr, v);
                }
                break;

        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (TypeCheck(ty, v__(t0->types, i), v)) {
                                return true;
                        }
                }
                return false;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!TypeCheck(ty, v__(t0->types, i), v)) {
                                return false;
                        }
                }
                return true;

        case TYPE_TUPLE:
                if (v->type == VALUE_TUPLE) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                char const *name = v__(t0->names, i);
                                Value const *item = (name == NULL) ? tuple_get(v, name)
                                                  : (v->count > i) ? &v->items[i]
                                                  : /*)  else  (*/   NULL;
                                if (item == NULL || !TypeCheck(ty, v__(t0->types, i), item)) {
                                        return false;
                                }
                        }
                } else {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                char const *name = v__(t0->names, i);
                                if (name == NULL) {
                                        return false;
                                }
                                int id = M_ID(name);
                                Value item = GetMember(ty, *v, id, false);
                                if (item.type == VALUE_BREAK) {
                                        item = CompleteCurrentFunction(ty);
                                }
                                if (
                                        item.type == VALUE_NONE
                                     || !TypeCheck(ty, v__(t0->types, i), &item)
                                ) {
                                        return false;
                                }
                        }
                }
                return true;

        case TYPE_TAG:
                return v->type == VALUE_TAG
                    && v->tag == TagOf(t0);

        case TYPE_CLASS:
                return v->type == VALUE_CLASS
                    && class_is_subclass(ty, v->class, t0->class->i);

        default:
                if (v->type & VALUE_TAGGED) {
                        if (TagOf(t0) != tags_first(ty, v->tags)) {
                                return false;
                        }
                        Value inner = unwrap(ty, v);
                        return TypeCheck(ty, TypeArg(t0, 0), &inner);

                } else if (t0->type == TYPE_OBJECT) {
                        if (!class_is_subclass(ty, ClassOf(v), t0->class->i)) {
                                return false;
                        }
                        switch (t0->class->i) {
                        case CLASS_ARRAY:
                                for (int i = 0; i < vN(*v->array); ++i) {
                                        if (
                                                !TypeCheck(
                                                        ty,
                                                        TypeArg(t0, 0),
                                                        v_(*v->array, i)
                                                )
                                        ) {
                                                return false;
                                        }
                                }
                                break;

                        case CLASS_DICT:
                                for (size_t i = 0; i < v->dict->size; ++i) {
                                        if (v->dict->keys[i].type == 0) {
                                                continue;
                                        }
                                        if (
                                                !TypeCheck(
                                                        ty,
                                                        TypeArg(t0, 0),
                                                        &v->dict->keys[i]
                                                )
                                        ) {
                                                return false;
                                        }
                                        if (
                                                !TypeCheck(
                                                        ty,
                                                        TypeArg(t0, 1),
                                                        &v->dict->values[i]
                                                )
                                        ) {
                                                return false;
                                        }
                                }
                                break;
                        }
                        return true;
                }
        }

        return false;
}
