#include "ty.h"
#include "types.h"
#include "class.h"
#include "intern.h"
#include "ast.h"
#include "compiler.h"
#include "operators.h"
#include "value.h"
#include "itable.h"

enum { CHECK_BIND, CHECK_NOBIND, CHECK_RUNTIME };

#undef NIL

#define ANY TYPE_ANY
#define BOTTOM BOTTOM_TYPE
#define NIL NIL_TYPE

#define CloneVec(v) (                                  \
        (v).items = memcpy(                            \
                mA((v).capacity * sizeof *(v).items),  \
                (v).items,                             \
                (v).count * sizeof *(v).items          \
        )                                              \
)

#define TypeError(...) CompileError(ty, __VA_ARGS__)
#define ShowType(t) type_show(ty, (t))

static Expr *
FindMethod(Class const *c, char const *name);

static Type *
TypeOf2Op(Ty *ty, int op, Type *t0, Type *t1);

static void
BindVars(Ty *ty, Type *t0, Type *t1, bool sub);

static void
BindChecked(Ty *ty, Type *t0, Type *t1);

static bool
BindConstraint(Ty *ty, Constraint const *c, bool check);

static void
FoldConstraints(Ty *ty);

static Type *
ResolveAlias(Ty *ty, Type *t0);

bool
type_check_x(Ty *ty, Type *t0, Type *t1, int mode);

Value *
vm_local(Ty *ty, int i);

static void
unify_(Ty *ty, Type **t0, Type *t1, bool fixed);

static Type *
ArrayOf(Ty *ty, Type *t0);

static Type *
DictOf(Ty *ty, Type *k0, Type *v0);

static Type *
ClassFunctionType(Ty *ty, Type *t0);

Type *TYPE_INT;
Type *TYPE_FLOAT;
Type *TYPE_BOOL;
Type *TYPE_STRING;
Type *TYPE_BLOB;
Type *TYPE_ARRAY;
Type *TYPE_DICT;
Type *NIL_TYPE;
Type *NONE_TYPE;
Type *TYPE_ANY;
Type *BOTTOM_TYPE;
Type *TYPE_CLASS_;

static u32 NextID = 0;
static u32 CurrentLevel = 0;

#define EnterScope() do {                                  \
        printf("===> ENTER\n");                            \
        xvP(ty->tcons, ((ConstraintVector){0}));           \
        ty->tenv = NewEnv(ty, ty->tenv);                   \
        ty->tscope = scope_new(ty, "", ty->tscope, false); \
} while (0)

#define LeaveScope() do {                       \
        FoldConstraints(ty);                    \
        printf("<=== LEAVE (%s)\n", __func__);  \
        ty->tscope = ty->tscope->parent;        \
        ty->tenv = ty->tenv->parent;            \
} while (0)

static TypeEnv *
NewEnv(Ty *ty, TypeEnv *parent)
{
        TypeEnv *env = amA0(sizeof *env);
        env->parent = parent;
        env->level = (parent != NULL) ? (parent->level +  1) : 0;
        return env;
}

inline static bool
already_visiting(TypeVector const *types, Type *t0)
{
        for (int i = 0; i < vN(*types); ++i) {
                if (t0 == v__(*types, i)) {
                        return true;
                }
        }

        return false;
}

inline static uint32_t
TypeType(Type const *t0)
{
        return (t0 == NULL) ? TYPE_BOTTOM : t0->type;
}

inline static uint64_t
PackTypes(Type const *t0, Type const *t1)
{
        return PACK_TYPES(TypeType(t0), TypeType(t1));
}

inline static bool
IsAny(Type *t0)
{
        if (((uintptr_t)t0 & 7) != 0) {
                *(char *)0 = 0;
        }
        return t0 != NULL
            && t0->type == TYPE_OBJECT
            && t0->class->i == CLASS_TOP;
}

inline static bool
IsBottom(Type *t0)
{
        return t0 == NULL || t0->type == TYPE_BOTTOM;
}

inline static bool
IsNil(Type *t0)
{
        return t0 != NULL
            && t0->type == TYPE_NIL;
}

inline static bool
IsVariadic(Type const *t0)
{
        if (t0 == NULL || t0->type != TYPE_FUNCTION) {
                return false;
        }

        for (int i = 0; i < vN(t0->fun_params); ++i) {
                if (v_(t0->fun_params, i)->rest) {
                        return true;
                }
        }

        return false;
}

inline static bool
IsKwVariadic(Type const *t0)
{
        if (t0 == NULL || t0->type != TYPE_FUNCTION) {
                return false;
        }

        for (int i = 0; i < vN(t0->fun_params); ++i) {
                if (v_(t0->fun_params, i)->kws) {
                        return true;
                }
        }

        return false;
}

static Type *
NewType(Ty *ty, int t)
{
        Type *type = amA0(sizeof *type);
        type->type = t;
        return type;
}

static Type *
NewVar(Ty *ty)
{
        Type *t0 = NewType(ty, TYPE_VARIABLE);
        t0->id = NextID++;
        t0->level = CurrentLevel;
}

static Scope *
FunTypeScope(Ty *ty)
{
        Scope *s = ty->tscope;

        while (s->parent != NULL && s->function != s) {
                s = s->parent;
        }

        return s;
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
        //var = scope_add(ty, TyCompilerState(ty)->func->scope, sclonea(ty, b));
        //var->type_var = true;
        //var->type = type_variable(ty, var);

        avP(t0->params, var);

        return var->type;
}

static Type *
AddScopedParam(Ty *ty, Type *t0)
{
        char b[32];
        Symbol *var;

        snprintf(b, sizeof b, "$%d", (int)vN(t0->params));
        //var = scope_add(ty, TyCompilerState(ty)->func->scope, sclonea(ty, b));
        //var->type_var = true;
        //var->type = type_variable(ty, var);
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
                t->fixed = false;
                if (t->type == TYPE_VARIABLE) {
                        t->mark = false;
                }
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
ParamCount(Type const *t0)
{
        if (t0 == NULL) {
                return 0;
        }

        switch (t0->type) {
        case TYPE_OBJECT:
        case TYPE_ALIAS:
        case TYPE_CLASS:
        case TYPE_FUNCTION:
                return vN(t0->params);
        }

        return 0;

}

inline static int
ArgCount(Type const *t0)
{
        if (t0 == NULL) {
                return 0;
        }

        switch (t0->type) {
        case TYPE_OBJECT:
        case TYPE_ALIAS:
        case TYPE_CLASS:
        case TYPE_FUNCTION:
                return vN(t0->args);
        }

        return 0;

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
        if (IsBottom(t0)) {
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
        if (IsBottom(t0)) {
                return CLASS_BOTTOM;
        }

        if (IsAny(t0)) {
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

static bool
IsCallable(Type *t0)
{
        if (t0 == NULL) {
                return true;
        } 

        if (IsAny(t0)) {
                return false;
        }

        return t0->type == TYPE_FUNCTION
            || t0->type == TYPE_TAG
            || t0->type == TYPE_CLASS
            || (
                        t0->type == TYPE_OBJECT
                     && type_find_member(ty, t0, "__call__") != NULL
               )
            ;
}

static Type *
UnionOf(Ty *ty, Type *t0)
{
        if (IsBottom(t0)) {
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

static bool
RefersTo(Type *t0, Symbol *var)
{
        if (IsBottom(t0)) {
                return false;
        }

        static TypeVector visiting;
        if (already_visiting(&visiting, t0)) {
                return true;
        } else {
                xvP(visiting, t0);
        }

        bool ret = false;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (t0->var->symbol == var->symbol) {
                        ret = true;
                } else if (t0->var->type == t0) {
                        ret = false;
                } else {
                        ret = RefersTo(t0->var->type, var);
                }
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (RefersTo(v__(t0->types, i), var)) {
                                ret = true;
                                break;
                        }
                }
                break;

        case TYPE_FUNCTION:
                if (RefersTo(t0->rt, var)) {
                        ret = true;
                        break;
                }
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        if (RefersTo(v_(t0->fun_params, i)->type, var)) {
                                ret = true;
                                break;
                        }
                }
        case TYPE_OBJECT:
        case TYPE_CLASS:
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (RefersTo(v__(t0->args, i), var)) {
                                ret = true;
                                break;
                        }
                }
                break;
        }

        vvX(visiting);

        return ret;
}

Type *
type_object(Ty *ty, Class *class)
{
        Type *t = NewType(ty, TYPE_OBJECT);
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
                        avP(t->args, t0);
                }
        }

        printf("type_object(%s) = %s (narg=%d)\n", class->name, ShowType(t), (int)vN(t->args));

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

        printf("================== %s ======================\n", e->name);

        if (e->return_type != NULL) {
                t->rt = type_fixed(ty, type_resolve(ty, e->return_type));
        }

        for (int i = 0; i < vN(e->type_params); ++i) {
                avP(t->params, v__(e->type_params, i)->symbol);
        }

        for (int i = 0; i < vN(e->param_symbols); ++i) {
                Symbol *psym = v__(e->param_symbols, i);
                if (psym->type == NULL) {
                        if (i == e->rest) {
                                psym->type = ArrayOf(ty, NULL);
                        } else if (i == e->ikwargs) {
                                psym->type = DictOf(ty, TYPE_STRING, NULL);
                        } else {
                                psym->type = AddScopedParam(ty, t);
                        }
                }
                avP(
                        t->fun_params,
                        PARAMx(
                                .var  = psym,
                                .type = psym->type,
                                .rest = (i == e->rest),
                                .kws  = (i == e->ikwargs),
                                .required = (
                                        v__(e->dflts, i) == NULL
                                     && (i != e->rest)
                                     && (i != e->ikwargs)
                                     && (
                                                v__(e->constraints, i) == NULL
                                             || v__(e->constraints, i)->type != EXPRESSION_PREFIX_QUESTION
                                        )
                                )
                        )
                );
                //psym->type = type_fixed(ty, psym->type);
        }

        if (e->function_symbol != NULL) {
                e->function_symbol->type = t;
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

static void
GatherBound(Ty *ty, Type *t0, U32Vector *bound)
{
        static int d = 0;

        printf("%*sGatherBound(%s)\n", 4*d, "", ShowType(t0));

        if (t0 == NULL) {
                return;
        }

        static TypeVector visiting;
        if (already_visiting(&visiting, t0)) {
                return;
        } else {
                xvP(visiting, t0);
        }

        d += 1;

        Symbol *var;
        Type *t1;
        Type *t2;
        bool cloned = false;

        Type *t_ = t0;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (t0->val != NULL) {
                        GatherBound(ty, t0->val, bound);
                } else if (t0->level > CurrentLevel) {
                        avP(*bound, t0->id);
                }
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        GatherBound(ty, v__(t0->types, i), bound);
                }
                break;

        case TYPE_OBJECT:
                for (int i = 0; i < vN(t0->args); ++i) {
                        t1 = v__(t0->args, i);
                        t2 = PropagateX(ty, t1, bound);
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
                        t1 = PropagateX(ty, p->type, bound);
                        if (t1 != p->type && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->fun_params);
                                cloned = true;
                        }
                        *v_(t0->fun_params, i) = *p;
                        v_(t0->fun_params, i)->type = t1;
                }
                t1 = PropagateX(ty, t0->rt, bound);
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

        printf("%*sPropagate(%s) => %s\n", d*4, "", ShowType(t_), ShowType(t0));

        vvX(visiting);

        return t0;
}

static Type *
PropagateX(Ty *ty, Type *t0, symbol_vector *bound)
{
        static int d = 0;

        printf("%*sPropagate(%s)\n", 4*d, "", ShowType(t0));

        if (t0 == NULL) {
                return NULL;
        }

        static TypeVector visiting;
        if (already_visiting(&visiting, t0)) {
                return t0;
        } else {
                xvP(visiting, t0);
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
                        t0 = BOTTOM;
                        goto ShortCircuit;
                } else {
                        t0->mark = true;
                }
                var = scope_find_symbol(ty->tscope, t0->var);
                if (var == NULL) {
                        if (t0->var->type != t0) {
                                t2 = PropagateX(ty, t0->var->type, bound);
                        } else {
                                if (bound != NULL) {
                                        avP(*bound, t0->var);
                                }
                                break;
                        }
                } else if (var == t0->var) {
                        if (bound != NULL) {
                                avP(*bound, var);
                        }
                        break;
                } else {
                        t2 = PropagateX(ty, var->type, bound);
                }
                t1 = t0;
                t0 = CloneType(ty, t2);
                for (int i = 0; i < vN(t1->args); ++i) {
                        avP(t0->args, PropagateX(ty, v__(t1->args, i), bound));
                }
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        t2 = PropagateX(ty, t1, bound);
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
                        t2 = PropagateX(ty, t1, bound);
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
                        t1 = PropagateX(ty, p->type, bound);
                        if (t1 != p->type && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->fun_params);
                                cloned = true;
                        }
                        *v_(t0->fun_params, i) = *p;
                        v_(t0->fun_params, i)->type = t1;
                }
                t1 = PropagateX(ty, t0->rt, bound);
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

        printf("%*sPropagate(%s) => %s\n", d*4, "", ShowType(t_), ShowType(t0));

        vvX(visiting);

        return t0;
}

static Type *
Propagate(Ty *ty, Type *t0)
{
        return PropagateX(ty, t0, NULL);
}

inline static bool
ContainsSymbol(symbol_vector const *vars, Symbol const *var)
{
        for (int i = 0; i < vN(*vars); ++i) {
                if (v__(*vars, i)->symbol == var->symbol) {
                        return true;
                }
        }

        return false;
}

static Type *
Generalize(Ty *ty, Type *t0)
{
        Type *t1 = t0;
        symbol_vector bound = {0};

        switch (TypeType(t0)) {
        case TYPE_FUNCTION:
                PropagateX(ty, t0, &bound);
                if (vN(bound) > 0) {
                        t1 = CloneType(ty, t0);
                        CloneVec(t1->params);
                        for (int i = 0; i < vN(bound); ++i) {
                                if (!ContainsSymbol(&t1->params, v__(bound, i))) {
                                        avP(t1->params, v__(bound, i));
                                }
                        }
                }
                break;
        }

        return t1;
}

static void
BindVarsX(Ty *ty, Type *t0, Type *t1, bool super)
{
        Symbol *var;
        Type *t2;

        printf("BindVar():\n  %s\n  %s\n", ShowType(t0), ShowType(t1));

        //t0 = Propagate(ty, t0);

        printf("BindVar(*):\n  %s\n  %s\n", ShowType(t0), ShowType(t1));

        if (t0 == NULL || t1 == NULL) {
                return;
        }

        if (t0->type != TYPE_VARIABLE && t1->type == TYPE_VARIABLE) {
                //BindVarsX(ty, t1, t0, !super);
                //return;
        }

        t1 = Propagate(ty, t1);

        if (
                t0->type == TYPE_VARIABLE
             && t1->type == TYPE_VARIABLE
             && t0->var->type == t1->var->type
        ) {
                return;
        }

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (RefersTo(Propagate(ty, t1), t0->var)) {
                        break;
                }
                if (vN(t0->args) == 0) {
                        var = scope_find_symbol(ty->tscope, t0->var);
                        if (var == NULL || var == t0->var) {
                                var = scope_insert(ty, ty->tscope, t0->var);
                                var->type = CloneType(ty, t1);
                                if (var->type != NULL) {
                                        v0(var->type->args);
                                }
                                var->type = Relax(Propagate(ty, t1));
                        } else if (t1->type != TYPE_VARIABLE || t1->var->type != t1) {
                                if (!super) {
                                        unify(ty, &var->type, Relax(Propagate(ty, t1)));
                                } else {
                                        type_intersect(ty, &var->type, Relax(Propagate(ty, t1)));
                                }
                        }
                        printf("BindVar(): %s := %s\n", var->identifier, ShowType(var->type));
                } else {
                        int extra = ArgCount(t1) - ArgCount(t0);
                        for (int i = 0; i < vN(t0->args); ++i) {
                                BindVarsX(
                                        ty,
                                        v__(t0->args, i),
                                        TypeArg(t1, i - vN(t0->args)),
                                        super
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
                        printf("BindVar(): %s := %s\n", var->identifier, ShowType(var->type));
                }
                break;

        case TYPE_OBJECT:
                for (int i = 0; i < ArgCount(t0) && i < ArgCount(t1); ++i) {
                        BindVarsX(ty, TypeArg(t0, i), TypeArg(t1, i), super);
                }
                if (t0->class->i >= CLASS_PRIMITIVE) {
                        ClassDefinition *def = &t0->class->def->class;
                        for (int i = 0; i < vN(def->fields); ++i) {
                                Expr *field = v__(def->fields, i);
                                Expr *id = (field->type == EXPRESSION_EQ)
                                         ? field->target
                                         : field;
                                Type *u = type_member_access_t(ty, t1, field->identifier);
                                if (IsBottom(u) || IsAny(u)) {
                                        continue;
                                }
                                Type *t = (id->constraint != NULL)
                                        ? type_resolve(ty, id->constraint)
                                        : field->value->_type;
                                BindVarsX(ty, t, u, super);
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
                                        BindVarsX(ty, v__(t0->types, i), t2, super);
                                }
                        }
                        for (int i = 0; i < vN(t1->types); ++i) {
                                char const *name = v__(t1->names, i);
                                t2 = (name != NULL)
                                   ? RecordField(ty, t0, name)
                                   : RecordElem(t0, i);
                                if (t2 != NULL) {
                                        BindVarsX(ty, v__(t0->types, i), t2, super);
                                }
                        }
                } else if (t1 != NULL && t1->type == TYPE_OBJECT) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                char const *name = v__(t0->names, i);
                                t2 = (name != NULL)
                                   ? type_member_access_t(ty, t1, name)
                                   : NULL;
                                if (t2 != NULL) {
                                        BindVarsX(ty, v__(t0->types, i), t2, super);
                                }
                        }
                }
                break;

        //                        T  -> U
        //  ($0 * Float -> $1) => $0 -> $1

        case TYPE_FUNCTION:
                if (t1 != NULL && t1->type == TYPE_CLASS) {
                        t1 = ClassFunctionType(ty, t1);
                }
                if (t1 != NULL && t1->type == TYPE_FUNCTION) {
                        for (int i = 0; i < vN(t0->fun_params); ++i) {
                                Param const *p0 = v_(t0->fun_params, i);
                                Param const *p1 = (vN(t1->fun_params) > i) ? v_(t1->fun_params, i) : NULL;
                                if (
                                        (p0->kws || p0->rest)
                                     || ((p1 != NULL) && (p1->kws || p1->rest))
                                ) {
                                        continue;
                                }
                                Type *t2 = (p1 == NULL) ? NIL_TYPE : p1->type;
                                BindVarsX(ty, p0->type, t2, super);
                        }
                        for (int i = 0; i < vN(t1->fun_params); ++i) {
                                Param const *p0 = (vN(t0->fun_params) > i) ? v_(t0->fun_params, i) : NULL;
                                Param const *p1 = v_(t1->fun_params, i);
                                if (
                                        (p1->kws || p1->rest)
                                     || ((p0 != NULL) && (p0->kws || p0->rest))
                                ) {
                                        continue;
                                }
                                Type *t2 = (p0 == NULL) ? NIL_TYPE : p0->type;
                                BindVarsX(ty, p1->type, t2, super);
                        }
                        for (int i = 0; i < vN(t0->constraints); ++i) {
                                BindConstraint(ty, v_(t0->constraints, i), super);
                        }
                        for (int i = 0; i < vN(t1->constraints); ++i) {
                                BindConstraint(ty, v_(t1->constraints, i), super);
                        }
                        BindVarsX(ty, t0->rt, t1->rt, super);
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

static void
BindVars(Ty *ty, Type *t0, Type *t1, bool checked)
{
        BindVarsX(ty, t0, t1, true);
        BindVarsX(ty, t1, t0, false);

        if (!checked) {
                return;
        }

        t0 = Propagate(ty, t0);
        t1 = Propagate(ty, t1);

        if (t0 == NULL || t1 == NULL) {
                return;
        }

        if (!type_check_x(ty, t0, t1, CHECK_NOBIND)) {
                TypeError(
                        "type error, can't bind: `%s` != `%s`",
                        ShowType(t0),
                        ShowType(t1)
                );
        }
}

static bool
BindConstraint(Ty *ty, Constraint const *c, bool check)
{
        Type *t0;
        Type *t1;
        Type *t2;

        switch (c->type) {
        case TC_2OP:
                t0 = Propagate(ty, c->t0);
                t1 = Propagate(ty, c->t1);
                t2 = Propagate(ty, c->rt);
                printf(
                        "BindConstraint(TC_2OP):\n  t0=%s\n  t1=%s\n  t2=%s\n",
                        ShowType(t0),
                        ShowType(t1),
                        ShowType(t2)
                );
                if (
                        IsConcrete(t0)
                     && IsConcrete(t1)
                     && IsConcrete(t2)
                ) {
                        return true;
                }
                if (
                        IsConcrete(t0)
                     && IsConcrete(t1)
                ) {
                        BindVars(
                                ty,
                                t2,
                                Propagate(ty, TypeOf2Op(ty, c->op, t0, t1)),
                                check
                        );

                        return true;
                }
                break;

        case TC_EQ:
                t0 = Propagate(ty, c->t0);
                t1 = Propagate(ty, c->t1);
                //BindVars(ty, t1, t0, false);
                BindVars(ty, t0, t1, check);
                break;

        }

        return true;
}

static void
UpdateEnv(Ty *ty)
{
        Scope *s = ty->tscope->parent;

        static TypeVector visiting;

        while (s != NULL) {
                for (int i = 0; i < 16; ++i) {
                        Symbol *var = s->table[i];
                        while (var != NULL) {
                                if (already_visiting(&visiting, var->type)) {
                                        continue;
                                }
                                xvP(visiting, var->type);
                                var->type = Propagate(ty, var->type);
                                vvX(visiting);
                                var = var->next;
                        }
                }

                if (s->function == s) {
                        break;
                }

                s = s->parent;
        }

}

static void
FoldConstraintsX(Ty *ty, ConstraintVector const *cons)
{
        for (int i = 0; i < vN(*cons); ++i) {
                Constraint *c = v_(*cons, i);
                c->t0 = Propagate(ty, c->t0);
        }
}

static void
FoldConstraints(Ty *ty)
{
        //UpdateEnv(ty);

        vvX(ty->tcons);

        if (vN(ty->tcons) > 0) {
                FoldConstraintsX(ty, vvL(ty->tcons));
        }

        if (
                TyCompilerState(ty)->func != NULL
             && TyCompilerState(ty)->func->_type != NULL
             && TyCompilerState(ty)->func->_type->type == TYPE_FUNCTION
        ) {
                FoldConstraintsX(ty, &TyCompilerState(ty)->func->_type->constraints);
        }
}

static void
ApplyConstraintsX(Ty *ty, ConstraintVector const *cons)
{
        printf("ApplyConstraints():\n");
        for (int i = 0; i < vN(*cons); ++i) {
                Constraint const *c = v_(*cons, i);
                switch (c->type) {
                case TC_EQ:
                        printf("============    %s  =  %s\n", ShowType(c->t0), ShowType(c->t1));
                        break;
                }
        }

        for (int i = 0; i < vN(*cons); ++i) {
                BindConstraint(ty, v_(*cons, i), false);
        }

        for (int i = 0; i < vN(*cons); ++i) {
                Constraint *c = v_(*cons, i);
                switch (c->type) {
                case TC_EQ:
                        c->t0 = Propagate(ty, c->t0);
                        break;
                }
        }
}

static void
ApplyConstraints(Ty *ty)
{
        if (vN(ty->tcons) > 0) {
                ApplyConstraintsX(ty, vvL(ty->tcons));
        }

        if (
                TyCompilerState(ty)->func != NULL
             && TyCompilerState(ty)->func->_type != NULL
             && TyCompilerState(ty)->func->_type->type == TYPE_FUNCTION
        ) {
                ApplyConstraintsX(ty, &TyCompilerState(ty)->func->_type->constraints);
        }
}



static Type *
ResolveAlias(Ty *ty, Type *t0)
{
        EnterScope();

        //char const *s0 = ShowType(t0);

        for (int i = 0; i < vN(t0->args) && i < vN(t0->params); ++i) {
                BindVars(ty, v__(t0->params, i)->type, v__(t0->args, i), true);
        }

        Type *t = Propagate(ty, t0->_type);

        printf("ResolveAlias(%s) = %s\n", ShowType(t0), ShowType(t));

        LeaveScope();

        return t;

}

static bool
CheckCallT(Ty *ty, TypeVector const *args, Type *t0)
{
        Type *t1;
        Type *t2;
        Expr *init;

        printf("CheckCallT(%s)\n", ShowType(t0));
        for (int i = 0; i < vN(*args); ++i) {
                printf("    %s\n", ShowType(v__(*args, i)));
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
                        if (i >= vN(*args)) {
                                if (v_(t0->fun_params, i)->required) {
                                        return false;
                                } else {
                                        continue;
                                }
                        }
                        t1 = v_(t0->fun_params, i)->type;
                        t2 = v__(*args, i);
                        if (!type_check_x(ty, t1, t2, CHECK_NOBIND)) {
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
                return (t1 == NULL) ? true : CheckCallT(ty, args, t1);

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        if (CheckCallT(ty, args, t1)) {
                                return true;
                        }
                }
        }

        return true;
}

static Type *
BindCallT(Ty *ty, TypeVector const *args, Type *t0)
{
        Type *t1;
        Type *t2;
        Expr *init;

        printf("BindCallT(%s)\n", ShowType(t0));
        for (int i = 0; i < vN(*args); ++i) {
                printf("    %s\n", ShowType(v__(*args, i)));
        }

        if (t0 == NULL) {
                return NULL;
        }

        switch (t0->type) {
        case TYPE_FUNCTION:
                for (int i = 0; i < vN(*args) && i < vN(t0->fun_params); ++i) {
                        Type *u0 = Relax(v_(t0->fun_params, i)->var->type);
                        Type *u1 = Relax(v__(*args, i));
                        //BindVars(ty, u1, u0, false);
                        BindVars(ty, u0, u1, true);
                }
                for (int i = vN(*args); i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (p->required) {
                                if (p->var != NULL) {
                                        TypeError(
                                                "missing argument for required parameter %s%s%s of type `%s`",
                                                TERM(93), p->var->identifier, TERM(0),
                                                ShowType(v_(t0->fun_params, i)->type)
                                        );
                                } else {
                                        TypeError(
                                                "missing argument for required parameter of type `%s`",
                                                ShowType(v_(t0->fun_params, i)->type)
                                        );
                                }
                        }
                }
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        BindConstraint(ty, v_(t0->constraints, i), true);
                }
                return t0->rt;

        case TYPE_CLASS:
                init = FindMethod(t0->class, "init");
                if (init == NULL) {
                        break;
                }

                t1 = init->_type;
                if (t1 != NULL) {
                        BindCallT(ty, args, t1);
                }

                t2 = t0->class->object_type;
                for (int i = 0; i < vN(t0->params); ++i) {
                        if (t2 == t0->class->object_type) {
                                t2 = CloneType(ty, t2);
                                CloneVec(t2->args);
                        }
                        Type *p0 = Propagate(ty, v__(t0->params, i)->type);
                        if (p0 == v__(t0->params, i)->type) {
                                p0 = GenScopedVar(ty);
                        }
                        avP(t2->args, p0);
                }

                return t2;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        if (CheckCallT(ty, args, t1)) {
                                return BindCallT(ty, args, t1);
                        }
                }
        }

        return NULL;
}


static Type *
ClassFunctionType(Ty *ty, Type *t0)
{
        Type *t1 = CloneType(ty, t0);
        t1->type = TYPE_OBJECT;

        Type *t2 = type_member_access_t(ty, t1, "init");

        if (!IsBottom(t2)) {
                if (t2->type == TYPE_FUNCTION) {
                        t2 = CloneType(ty, t2);
                        t2->rt = t1;
                } else if (t2->type == TYPE_INTERSECT) {
                        t2 = CloneType(ty, t2);
                        CloneVec(t2->types);
                        for (int i = 0; i < vN(t2->types); ++i) {
                                Type *t = v__(t2->types, i);
                                if (t != NULL && t->type == TYPE_FUNCTION) {
                                        t = CloneType(ty, t);
                                        t->rt = t1;
                                }
                                *v_(t2->types, i) = t;
                        }
                }
        }

        return t2;
}

static bool
CheckCall(Ty *ty, expression_vector const *args, Type *t0)
{
        Type *t1;
        Type *t2;
        Expr *init;

        printf("CheckCall(%s)\n", ShowType(t0));
        for (int i = 0; i < vN(*args); ++i) {
                printf("    %s\n", ShowType(v__(*args, i)->_type));
        }

        if (t0 == NULL) {
                return true;
        }

        switch (t0->type) {
        case TYPE_FUNCTION:
                if (vN(*args) > vN(t0->fun_params) && !IsVariadic(t0)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (p->kws || p->rest) {
                                continue;
                        }
                        if (i >= vN(*args)) {
                                if (p->required) {
                                        return false;
                                } else {
                                        continue;
                                }
                        }
                        t1 = v_(t0->fun_params, i)->type;
                        t2 = v__(*args, i)->_type;
                        if (!type_check_x(ty, t1, t2, CHECK_NOBIND)) {
                                return false;
                        }
                }
                return true;

        case TYPE_CLASS:
                t1 = ClassFunctionType(ty, t0);
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

        printf("BindCall(%s)\n", ShowType(t0));
        for (int i = 0; i < vN(*args); ++i) {
                printf("    %s\n", ShowType(v__(*args, i)->_type));
        }

        if (t0 == NULL) {
                return NULL;
        }

        switch (t0->type) {
        case TYPE_FUNCTION:
                for (int i = 0; i < vN(*args) && i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (p->rest || p->kws) {
                                continue;
                        }
                        Type *p0 = Relax(Propagate(ty, v_(t0->fun_params, i)->type));
                        Type *p1 = Relax(Propagate(ty, v__(*args, i)->_type));
                        //BindVars(ty, p1, p0, false);
                        //p0 = Relax(Propagate(ty, p0));
                        //p1 = Relax(Propagate(ty, p1));
                        BindVars(ty, p0, p1, true);
                }
                for (int i = vN(*args); i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (p->rest || p->kws) {
                                continue;
                        }
                        if (p->required) {
                                if (p->var != NULL) {
                                        TypeError(
                                                "missing argument for required parameter %s%s%s of type `%s`",
                                                TERM(93), p->var->identifier, TERM(0),
                                                ShowType(v_(t0->fun_params, i)->type)
                                        );
                                } else {
                                        TypeError(
                                                "missing argument for required parameter of type `%s`",
                                                ShowType(v_(t0->fun_params, i)->type)
                                        );
                                }
                        }
                }
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        BindConstraint(ty, v_(t0->constraints, i), true);
                }

                return t0->rt;

        case TYPE_CLASS:
                return BindCall(ty, args, ClassFunctionType(ty, t0));

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

        t = Propagate(ty, BindCall(ty, args, t0));

        printf("SolveCall(%s): %s\n", ShowType(t0), ShowType(t));
        for (int i = 0; i < vN(*args); ++i) {
                printf("    %s\n", ShowType(v__(*args, i)->_type));
        }

        return t;
}

static Type *
type_call_t(Ty *ty, Expr const *e, Type *t0)
{
        if (IsBottom(t0)) {
                return BOTTOM;
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
                printf("(0) %s\n", t0->var->identifier);
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
                                        PARAM(NULL, v__(*args, i)->_type, true)
                                );
                        }
                        printf("(1) %s := %s\n", t0->var->identifier, ShowType(t0->var->type));
                        printf("(2) %s := %s\n", var->identifier, ShowType(var->type));
                        return var->type->rt;
                }
        }

        return NULL;
}

Type *
type_call(Ty *ty, Expr const *e)
{
        //EnterScope();
        Type *t0 = type_call_t(ty, e, e->function->_type);
        printf("type_call()\n");
        printf("    >>> %s\n", show_expr(e));
        printf("    %s\n", ShowType(t0));
        //printf("SolveCall(%s, %s) = %s\n", show_expr(e), ShowType(t0), ShowType(t));
        //LeaveScope();
        ApplyConstraints(ty);
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
Inst(Ty *ty, Type *t0, symbol_vector const *params)
{
        bool skip = true;
        for (int i = 0; i < vN(*params); ++i) {
                if (RefersTo(t0, v__(*params, i)->type->var)) {
                        skip = false;
                        break;
                }
        }

        if (skip) {
                printf("Inst(): SKIP  %s\n", ShowType(t0));
                return t0;
        }
        
        TypeVector vars = {0};
        for (int i = 0; i < vN(*params); ++i) {
                avP(vars, GenScopedVar(ty));
        }

        Scope *save = ty->tscope;
        ty->tscope = scope_new(ty, "", NULL, true);

        for (int i = 0; i < vN(*params); ++i) {
                Symbol *var = scope_insert(
                        ty,
                        ty->tscope,
                        v__(*params, i)
                );
                var->type = v__(vars, i);
        }

        t0 = Propagate(ty, t0);

        ty->tscope = save;

        return t0;
}

Type *
SolveMemberAccess(Ty *ty, Type *t0, Type *t1)
{
        Type *t;
        Symbol *var;

        return Generalize(ty, Inst(ty, t1, &t0->class->type->params));

        EnterScope();

        for (int i = 0; i < vN(t0->args) && i < vN(t0->class->type->params); ++i) {
                var = scope_insert(
                        ty,
                        ty->tscope,
                        v__(t0->class->type->params, i)
                );
                var->type = v__(t0->args, i);
                printf("SolveMemberAccess(): %s := %s  (args=%zu, params=%zu)\n", var->identifier, ShowType(var->type), vN(t0->args), vN(t0->params));
        }

        ClassDefinition *def = &t0->class->def->class;

        for (int i = 0; i < vN(def->traits); ++i) {
                Type *trait = type_resolve(ty, v__(def->traits, i));
                if (trait == NULL || trait->type != TYPE_OBJECT) {
                        continue;
                }
                for (int i = 0; i < ParamCount(trait->class->type); ++i) {
                        var = scope_insert(
                                ty,
                                ty->tscope,
                                v__(trait->class->type->params, i)
                        );
                        var->type = Propagate(ty, TypeArg(trait, i));
                        printf("SolveMemberAccess(): %s := %s  (args=%zu, params=%zu)\n", var->identifier, ShowType(var->type), vN(t0->args), vN(t0->params));
                }
        }

        ApplyConstraints(ty);

        t = Propagate(ty, t1);
        printf("SolveMemberAccess(%s): %s\n", ShowType(t1), ShowType(t));

        LeaveScope();

        return t;
}

Type *
type_member_access_t(Ty *ty, Type *t0, char const *name)
{
        printf("member_access(%s, %s)\n", ShowType(t0), name);

        if (IsAny(t0) || IsBottom(t0)) {
                return BOTTOM;
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
                        printf("(1) %s := %s\n", t0->var->identifier, ShowType(t0->var->type));
                        printf("(2) %s := %s\n", var->identifier, ShowType(var->type));
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
        EnterScope();

        Type *t0 = e->type == EXPRESSION_DYN_MEMBER_ACCESS
                 ? BOTTOM //UnionOf(ty, e->object->_type)
                 : type_member_access_t(ty, e->object->_type, e->member_name);

        ApplyConstraints(ty);
        t0 = Propagate(ty, t0);

        LeaveScope();

        return t0;
}

Type *
type_method_call_t(Ty *ty, Expr const *e, Type *t0, char const *name)
{
        if (IsNil(t0)) {
                return NIL;
        }

        if (IsBottom(t0) || e->type == EXPRESSION_DYN_METHOD_CALL) {
                return NULL;
        }

        Class *c;
        Expr *f;
        Type *t;

        switch (t0->type) {
        case TYPE_OBJECT:
                t = type_member_access_t(ty, t0, name);
                t = Propagate(ty, Inst(ty, type_call_t(ty, e, t), &t0->class->type->params));
                return t;

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
        EnterScope();

        Type *t1 = type_method_call_t(ty, &(Expr){ .type = EXPRESSION_METHOD_CALL }, t0, name);
        ApplyConstraints(ty);
        t1 = Propagate(ty, t1);
        printf("type_method_call_name()\n");
        printf("    %s\n", name);
        printf("    %s\n", ShowType(t0));
        printf("    %s\n", ShowType(t1));

        LeaveScope();

        return t1;
}

Type *
type_method_call(Ty *ty, Expr const *e)
{
        EnterScope();

        Type *t0 = type_method_call_t(ty, e, e->object->_type, e->method_name);
        ApplyConstraints(ty);
        t0 = Propagate(ty, t0);
        printf("type_method_call(%s)\n", e->method_name);
        printf("    >>> %s\n", show_expr(e));
        printf("    %s\n", ShowType(e->object->_type));
        printf("    %s\n", ShowType(t0));

        LeaveScope();

        return t0;
}

Type *
type_tagged(Ty *ty, int tag, Type *t0)
{
        Type *t1 = NewType(ty, TYPE_OBJECT);

        t1->class = tags_get_class(ty, tag);
        avP(t1->args, t0);

        if (t1->class == NULL) {
                printf("=== %s ===\n", tags_name(ty, tag));
                *(char *)0 = 0;
        }

        return t1;
}

Type *
type_generator(Ty *ty, Expr const *e)
{
        Type *t0 = NewType(ty, TYPE_OBJECT);
        t0->class = class_get_class(ty, CLASS_GENERATOR);
        avP(t0->args, TypeArg(e->_type->rt, 0));
        return t0;
}

Type *
type_subscript_t(Ty *ty, Type *t0, Type *t1)
{
        Type *t = NULL;
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

        printf("subscript(%s): %s\n", ShowType(t0), ShowType(t));

        return t;
}

Type *
type_subscript(Ty *ty, Expr const *e)
{
        return type_subscript_t(ty, e->container->_type, e->subscript->_type);
}

static bool
check_entry(Ty *ty, Type *t0, int i, Type *t1, int mode)
{
        if (IsBottom(t0)) {
                return false;
        }

        switch (t0->type) {
        case TYPE_UNION:
                for (int ii = 0; ii < vN(t0->types); ++ii) {
                        if (!check_entry(ty, v__(t0->types, ii), i, t1, mode)) {
                                return false;
                        }
                }
                return true;

        case TYPE_TUPLE:
                return vN(t0->types) > i
                    && type_check_x(ty, v__(t0->types, i), t1, mode);
        }

        return false;
}

static bool
check_field(Ty *ty, Type *t0, char const *name, Type *t1, int mode)
{
        if (IsBottom(t0)) {
                return false;
        }

        Value const *field;
        Expr const *m;

        switch (t0->type) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!check_field(ty, v__(t0->types, i), name, t1, mode)) {
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
                                return type_check_x(ty, v__(t0->types, i), t1, mode);
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
                                mode
                        );
                }
                m = FindMethod(t0->class, name);
                if (m != NULL) {
                        return type_check_x(ty, m->_type, t1, mode);
                }
        }

        return false;
}

static int d = 0;
//#define print(fmt, ...) printf("%*s" fmt "\n", d*4, "", __VA_ARGS__ + 0)
#define print(...) 0

bool
type_check_x_(Ty *ty, Type *t0, Type *t1, int mode)
{
        if (IsAny(t0) || t0 == t1 || IsBottom(t1) || IsBottom(t0)) {
                return true;
        }

        if (IsAny(t1)) {
                return false;
        }

        if (IsNil(t0) && IsNil(t1)) {
                return true;
        }

        if (t0 == NONE_TYPE || t1 == NONE_TYPE) {
                return true;
        }

        if (t0->type == TYPE_TAG && t1->type == TYPE_TAG) {
                return TagOf(t0) == TagOf(t1);
        }

        if (
                t0->type == TYPE_OBJECT
             && t0->class->i == CLASS_CLASS
             && t1->type == TYPE_CLASS
        ) {
                return true;
        }

        if (
                t0->type == TYPE_OBJECT
             && t0->class->i == CLASS_FUNCTION
             && IsCallable(t1)
        ) {
                return true;
        }

        if (
                t1->type == TYPE_OBJECT
             && t1->class->i == CLASS_FUNCTION
             && IsCallable(t0)
        ) {
                return true;
        }

        if (
               t0->type == TYPE_VARIABLE
            && t1->type == TYPE_VARIABLE
        ) {
                t0 = Propagate(ty, t0);
                t1 = Propagate(ty, t1);
                if (t0->type == TYPE_VARIABLE && t1->type == TYPE_VARIABLE) {
                        if (t0->var->symbol == t1->var->symbol) {
                                return true;
                        } else if (mode == CHECK_RUNTIME && TyCompilerState(ty)->func != NULL) {
                                Type *ft = TyCompilerState(ty)->func->_type;
                                avP(
                                        ft->constraints,
                                        ((Constraint){
                                                .type = TC_EQ,
                                                .t0 = t0,
                                                .t1 = t1
                                        })
                                );
                                return true;
                        }
                            //|| t0->var->type == t0
                            //|| t1->var->type == t1;
                } else {
                        return type_check_x(ty, t0, t1, CHECK_NOBIND); // && type_check_x(ty, t0, t1, mode);
                }
        }

        if (
                (t0->type == TYPE_VARIABLE && RefersTo(Propagate(ty, t1), t0->var))
             || (t1->type == TYPE_VARIABLE && RefersTo(Propagate(ty, t0), t1->var))
        ) {
                return true;
        }

        if (false && t0->type == TYPE_VARIABLE) {
                Symbol *var = scope_find_symbol(ty->tscope, t0->var);
                if (
                        var == NULL
                     && TyCompilerState(ty)->func != NULL
                ) {
                        var = scope_find_symbol(TyCompilerState(ty)->func->scope, t0->var);
                }
                //if ((var == NULL && mode == CHECK_NOBIND) || var != NULL || mode == CHECK_BIND) {
                return var == NULL || var->type == t0;
                if (var == NULL | mode == CHECK_BIND) {
                        Type *t0_ = (var == NULL) ? NULL : var->type;
                        if (t0_ == NULL || t0_ == t0->var->type || t0_ == t0) {
                                if (t0_ != NULL && mode == CHECK_NOBIND) {
                                        return true;
                                }
                                Symbol *var = scope_insert(ty, ty->tscope, t0->var);
                                var->type = CloneType(ty, t1);
                                if (var->type != NULL) {
                                        v0(var->type->args);
                                }
                                var->type = Relax(Propagate(ty, var->type));
                        } else if (!var->fixed && mode == CHECK_BIND) {
                                printf("OK 2\n");
                                unify(ty, &var->type, t1);
                                return true;

                        }
                        if (vN(t0_->args) != ArgCount(t1)) {
                                printf("ArgCount(t0_) = %d =/= ArgCount(t1) = %d\n", ArgCount(t0_), ArgCount(t1));
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
                        return type_check_x(ty, t0_, t1, mode);
                } else if (mode == CHECK_NOBIND) {
                        return true;
                } else if (mode == CHECK_RUNTIME) {
                        var = scope_insert(ty, ty->tscope, t0->var);
                        var->type = t1;
                        return true;
                        //Value *var = vm_load(ty, t0->var);
                        //printf("Load %s (%p): %s\n", t0->var->identifier, (void *)t0->var, VSC(var));
                        //printf("  t0: %s\n", ShowType(t0));
                        //printf("  t1: %s\n", ShowType(t1));
                        //if (var->type == VALUE_NIL || (Type *)var->ptr == t0) {
                        //        *var = TYPE(t1);
                        //        printf("After store: %s\n", VSC(var));
                        //        return true;
                        //} else {
                        //        return type_check_x(ty, var->ptr, t1, CHECK_RUNTIME);
                        //}
                }
        }

        if (false && t1->type == TYPE_VARIABLE) {
                Symbol *var = scope_find_symbol(ty->tscope, t1->var);
                if (
                        var == NULL
                     && TyCompilerState(ty)->func != NULL
                ) {
                        var = scope_find_symbol(TyCompilerState(ty)->func->scope, t1->var);
                }
                return var == NULL || var->type == t1;
                if (var == NULL) {
                        if (mode == CHECK_RUNTIME) {
                                var = scope_insert(ty, ty->tscope, t1->var);
                                var->type = t0;
                                return true;
                                //Value *var = vm_load(ty, t1->var);
                                //printf("Load %s (%p): %s\n", t1->var->identifier, (void *)t1->var, VSC(var));
                                //printf("  t0: %s\n", ShowType(t0));
                                //printf("  t1: %s\n", ShowType(t1));
                                //if (var->type == VALUE_NIL || (Type *)var->ptr == t1) {
                                //        *var = TYPE(t0);
                                //        printf("After store: %s\n", VSC(var));
                                //        return true;
                                //} else {
                                //        return type_check_x(ty, t0, var->ptr, CHECK_RUNTIME);
                                //}
                        } else {
                                return mode == CHECK_NOBIND;
                        }
                }
                printf(":::> %s (%d) :: %s (fixed=%d)  (mode=%d)\n", var->identifier, var->symbol, ShowType(var->type), var->fixed, mode);
                Type *t1_ = (var == NULL) ? NULL : var->type;
                if (t1_ == NULL || t1_ == t1->var->type || t1_ == t1) {
                        printf("OK\n");
                        if (mode == CHECK_NOBIND) {
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
                if (!var->fixed && mode == CHECK_BIND) {
                        printf("OK 2\n");
                        unify(ty, &var->type, t0);
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
                return type_check_x(ty, t1_, t0, mode);
        }

        if (t0->type == TYPE_UNION && t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (!type_check_x(ty, t0, v__(t1->types, i), mode)) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_INTERSECT && t1->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        bool ok = false;
                        for (int j = 0; j < vN(t1->types); ++j) {
                                if (
                                        type_check_x(
                                                ty,
                                                v__(t1->types, j),
                                                v__(t0->types, i),
                                                mode
                                        )
                                ) {
                                        ok = true;
                                        break;
                                }
                        }
                        if (!ok) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_INTEGER && t1->type == TYPE_INTEGER) {
                return t0->z == t1->z;
        }

        if (t1->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (type_check_x(ty, t0, v__(t1->types, i), mode)) {
                                return true;
                        }
                }
                return false;
        }

        if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (!type_check_x(ty, t0, v__(t1->types, i), mode)) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_UNION) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (type_check_x(ty, v__(t0->types, i), t1, mode)) {
                                return true;
                        }
                }
                return false;
        }

        if (t0->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!type_check_x(ty, v__(t0->types, i), t1, mode)) {
                                return false;
                        }
                }
                return true;
        }

        if (t1->type == TYPE_OBJECT) {
                ClassDefinition *def = &t1->class->def->class;
                for (int i = 0; i < vN(def->traits); ++i) {
                        if (
                                type_check_x(
                                        ty,
                                        t0,
                                        type_resolve(ty, v__(def->traits, i)),
                                        mode
                                )
                        ) {
                                return true;
                        }
                }
                if (
                        def->super != NULL
                     && type_check_x(
                                ty,
                                t0,
                                type_resolve(ty, def->super),
                                mode
                        )
                ) {
                        return true;
                }
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
                                        mode
                                )
                        ) {
                                return false;
                        }
                }
                return true;
        }
        
        if (t0->type == TYPE_TUPLE) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        char const *name = v__(t0->names, i);
                        if (
                                name == NULL
                              ? !check_entry(ty, t1, i, v__(t0->types, i), mode)
                              : !check_field(ty, t1, name, v__(t0->types, i), mode)
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
                              ? !check_entry(ty, t0, i, v__(t1->types, i), mode)
                              : !check_field(ty, t0, name, v__(t1->types, i), mode)
                        ) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_FUNCTION && t1->type == TYPE_CLASS) {
                t1 = ClassFunctionType(ty, t1);
        }

        if (t1->type == TYPE_FUNCTION && t0->type == TYPE_CLASS) {
                t0 = ClassFunctionType(ty, t0);
        }

        if (t0->type == TYPE_FUNCTION && t1->type == TYPE_FUNCTION) {
                EnterScope();
                for (int i = 0; i < vN(t0->fun_params) && i < vN(t1->fun_params); ++i) {
                        Param const *pp0 = v_(t0->fun_params, i);
                        Param const *pp1 = v_(t1->fun_params, i);
                        if (
                                (pp0->rest ^ pp1->rest)
                             || (pp0->kws ^ pp1->kws)
                        ) {
                                continue;
                        }
                        Type *p0 = Relax(Propagate(ty, pp0->type));
                        Type *p1 = Relax(Propagate(ty, pp1->type));
                        //BindVars(ty, p1, p0, false);
                        BindVars(ty, p0, p1, false);
                        if (!type_check_x(ty, p1, p0, CHECK_NOBIND)) {
                                LeaveScope();
                                return false;
                        }
                }
                for (int i = vN(t1->fun_params); i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (p->required && !p->kws && !p->rest) {
                                LeaveScope();
                                return false;
                        }
                }
                ApplyConstraints(ty);
                Type *r0 = Propagate(ty, t0->rt);
                Type *r1 = Propagate(ty, t1->rt);
                //BindVars(ty, r1, r0, false);
                BindVars(ty, r0, r1, false);
                r0 = Propagate(ty, r0);
                r1 = Propagate(ty, r1);
                if (!type_check_x(ty, r1, r0, CHECK_NOBIND)) {
                        LeaveScope();
                        return false;
                } else {
                        LeaveScope();
                        return true;
                }
#if 0

                for (int i = 0; i < max(vN(t0->fun_params), vN(t1->fun_params)); ++i) {
                        Type *a0 = (vN(t0->fun_params) > i)
                                 ? v_(t0->fun_params, i)->type
                                 : NIL_TYPE;
                        Type *a1 = (vN(t1->fun_params) > i)
                                 ? v_(t1->fun_params, i)->type
                                 : NIL_TYPE;
                        if (!type_check_x(ty, a1, a0, CHECK_RUNTIME)) {
                                return false;
                        }
                }
                return type_check_x(ty, t0->rt, t1->rt, mode);
#endif
        }

        return false;
}

bool type_check_x(Ty *ty, Type *t0, Type *t1, int mode)
{
        static int d = 0;
        printf("%*stype_check(%s):\n", 4*d, "", mode == CHECK_BIND ? "bind" : "");
        printf("%*s    %s\n", 4*d, "", ShowType(t0));
        printf("%*s    %s\n", 4*d, "", ShowType(t1));
        d += 1;
        bool b;
        if (mode != CHECK_NOBIND) {
                b = (d > 16) ? true : type_check_x_(ty, t0, t1, mode);
        } else {
                //EnterScope();
                b = (d > 16) ? true : type_check_x_(ty, t0, t1, CHECK_NOBIND);
                //LeaveScope();
        }
        d -= 1;
        printf("%*s => %s\n", 4*d, "", b ? "true" : "false");
        return b;
}


bool
type_check(Ty *ty, Type *t0, Type *t1)
{
        d += 1;
        //ty->tscope = scope_new(ty, "", ty->tscope, true);
        bool b = type_check_x(ty, t0, t1, CHECK_BIND);
        //LeaveScope();
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

static Type *
DictOf(Ty *ty, Type *k0, Type *v0)
{
        Type *t = CloneType(ty, TYPE_DICT);

        CloneVec(t->args);
        v0(t->args);

        Type *t1 = GenVar(ty);
        Type *t2 = GenVar(ty);

        if (!IsBottom(k0) && vN(ty->tcons) != 0) {
                ConstraintVector *cons = vvL(ty->tcons);
                avP(
                        *cons,
                        ((Constraint){
                                .type = TC_EQ,
                                .t0 = k0,
                                .t1 = t1
                        })
                );
        }

        if (!IsBottom(v0) && vN(ty->tcons) != 0) {
                ConstraintVector *cons = vvL(ty->tcons);
                avP(
                        *cons,
                        ((Constraint){
                                .type = TC_EQ,
                                .t0 = v0,
                                .t1 = t2
                        })
                );
        }

        avP(t->args, t1);
        avP(t->args, t2);

        return t;
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

        Type *t = NewType(ty,  TYPE_OBJECT);
        t->class = class_get_class(ty, CLASS_DICT);
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

        Type *t1 = GenScopedVar(ty);

        if (!IsBottom(t0) && vN(ty->tcons) != 0) {
                ConstraintVector *cons = vvL(ty->tcons);
                avP(
                        *cons,
                        ((Constraint){
                                .type = TC_EQ,
                                .t0 = t1,
                                .t1 = t0
                        })
                );
        }

        avP(t->args, t1);

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
type_assign(Ty *ty, Expr *e, Type *t0, bool fixed)
{
        if (t0 == NULL) {
                t0 = BOTTOM;
        }

        printf("assign(%s)\n", fixed ? "fixed" : "");
        printf("    %s\n", ShowType(t0));
        printf("    %s\n", show_expr(e));

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_RESOURCE_BINDING:
                if (!e->symbol->fixed) {
                        unify(ty, &e->_type, t0);
                        unify_(ty, &e->symbol->type, t0, e->symbol->fixed);
                        e->symbol->fixed |= fixed;
                        printf("type(%s) := %s  ==>  %s\n", e->symbol->identifier, ShowType(t0), ShowType(e->symbol->type));
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                for (int i = 0; i < UnionCount(t0); ++i) {
                        Type *t1 = UnionElem(t0, i);
                        printf("type_assign(): t1 = %s\n", ShowType(t1));
                        if (IsTagged(t1) && TagOf(t1) == e->symbol->tag) {
                                printf("type_assign(): %s |= %s\n", ShowType(e->tagged->_type), ShowType(t1));
                                type_assign(ty, e->tagged, TypeArg(t1, 0), fixed);
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
                                        type_subscript_t(ty, t0, TYPE_INT),
                                        fixed
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
                                        vN(t0->types) > i ? v__(t0->types, i) : BOTTOM,
                                        fixed
                                );
                        }
                }
                break;
        case EXPRESSION_LIST:
                type_assign(ty, v__(e->es, 0), t0, fixed);
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

        printf("Resolve(): %s\n", show_expr(e));

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (e->symbol == NULL) {
                        t0 = NULL;
                } else if (e->symbol->class != -1) {
                        t0 = NewType(ty, TYPE_OBJECT);
                        t0->class = class_get_class(ty, e->symbol->class);
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
                printf("resolve(): %s -> %s\n", e->identifier, ShowType(t0));
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
                printf("resolve_subscript(): -> %s\n", ShowType(t0));
                return Propagate(ty, t0);

        case EXPRESSION_TUPLE:
                t0 = NewType(ty, TYPE_TUPLE);
                for (int i = 0; i < vN(e->es); ++i) {
                        avP(t0->names, v__(e->names, i));
                        avP(t0->types, type_resolve(ty, v__(e->es, i)));
                }
                return t0;

        case EXPRESSION_BIT_OR:
                t0 = type_resolve(ty, e->left);
                if (t0 != NULL && t0->fixed) {
                        t0 = CloneType(ty, t0);
                }
                unify2(ty, &t0, type_resolve(ty, e->right));
                return t0;

        case EXPRESSION_BIT_AND:
                t0 = type_resolve(ty, e->left);
                type_intersect(ty, &t0, type_resolve(ty, e->right));
                return t0;

        case EXPRESSION_PREFIX_QUESTION:
                t0 = type_resolve(ty, e->operand);
                unify(ty, &t0, NIL_TYPE);
                return t0;

        case EXPRESSION_FUNCTION:
                t0 = NewType(ty, TYPE_FUNCTION);
                t0->rt = type_resolve(ty, v__(e->body->returns, 0));
                return t0;

        case EXPRESSION_FUNCTION_TYPE:
                t0 = NewType(ty, TYPE_FUNCTION);
                if (e->left->type == EXPRESSION_LIST) {
                        for (int i = 0; i < vN(e->left->es); ++i) {
                                avP(
                                        t0->fun_params,
                                        PARAM(
                                                NULL,
                                                type_resolve(
                                                        ty,
                                                        v__(e->left->es, i)
                                                ),
                                                true
                                        )
                                );
                        }
                } else if (e->left->type == EXPRESSION_TUPLE) {
                        for (int i = 0; i < vN(e->left->es); ++i) {
                                Symbol *name = amA0(sizeof *name);
                                name->identifier = vN(e->left->names) > i
                                                 ? v__(e->left->names, i)
                                                 : NULL;
                                avP(
                                        t0->fun_params,
                                        PARAM(
                                                name->identifier == NULL ? NULL : name,
                                                type_resolve(
                                                        ty,
                                                        v__(e->left->es, i)
                                                ),
                                                true
                                        )
                                );
                        }
                } else {
                        avP(t0->fun_params, PARAM(NULL, type_resolve(ty, e->left), true));
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

        printf("resolve() failed: %s\n", show_expr(e));

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
unify2(Ty *ty, Type **t0, Type *t1)
{
        printf("unify2()\n");
        printf("    %s\n", ShowType(*t0));
        printf("    %s\n", ShowType(t1));

        if (t1 == NULL) {
                t1 = BOTTOM;
        }

        if (*t0 == NULL || *t0 == BOTTOM || IsAny(t1) || *t0 == NONE_TYPE) {
                *t0 = type_unfixed(ty, t1);
                return;
        }

        if (type_check_x(ty, *t0, t1, CHECK_NOBIND)) {
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
                unify2(ty, v_((*t0)->args, 0), v__(t1->args, 0));
        } else if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        unify2(ty, t0, v__(t1->types, i));
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

static void
unify_(Ty *ty, Type **t0, Type *t1, bool fixed)
{
        printf("unify()\n");
        printf("    %s\n", ShowType(*t0));
        printf("    %s\n", ShowType(t1));

        if (t1 == NULL) {
                t1 = BOTTOM;
        }

        if (*t0 == NULL || *t0 == BOTTOM || IsAny(t1) || *t0 == NONE_TYPE) {
                *t0 = type_unfixed(ty, t1);
                return;
        }

        if (type_check_x(ty, *t0, t1, CHECK_NOBIND)) {
                return;
        }

        if (!fixed && !(*t0)->fixed) {
                BindVars(ty, *t0, t1, false);
                if (type_check_x(ty, Propagate(ty, *t0), Propagate(ty, t1), CHECK_NOBIND)) {
                        return;
                }
        } else if (!(*t0)->fixed){
                TypeError("type error: `%s` != `%s`", ShowType(*t0), ShowType(t1));
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
                unify_(ty, v_((*t0)->args, 0), v__(t1->args, 0), fixed);
        } else if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        unify_(ty, t0, v__(t1->types, i), fixed);
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
        //char const *s0 = ShowType(*t0);
        //char const *s1 = ShowType(t1);
        //printf("%*sunify(%s, %s)\n", d*4, "", s0, s1);
        d += 1;
        unify_(ty, t0, t1, false);
        d -= 1;
        //printf("%*sunify(%s, %s)  =>  %s\n", d*4, "", s0, s1, ShowType(*t0));
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

static struct itable VarNameTable;
static int VarLetter = 'a';
static int VarNumber = 0;

static char *
VarName(Ty *ty, u32 id)
{
        Value *v = itable_get(ty, &VarNameTable, id);

        if (v->type == VALUE_NIL) {
                byte_vector name = {0};
                dump(&name, "%c", VarLetter);
                if (VarNumber > 0) {
                        dump(&name, "%d", VarNumber);
                }
                if (VarLetter++ == 'z') {
                        VarLetter = 'a';
                        VarNumber += 1;
                }
                *v = PTR(name.items);
        }

        return v->ptr;
}

char *
type_show(Ty *ty, Type *t0)
{
        static int dt = 0;

        dt += 1;

        if (dt > 20) { *(char *)0 = 0; }

        if (IsBottom(t0)) {
                dt -= 1;
                return sclone_malloc("🔴");
        }

        static TypeVector visiting;
        if (already_visiting(&visiting, t0)) {
                dt -= 1;
                return sclone_malloc("...");
        } else {
                xvP(visiting, t0);
        }

        Symbol *var;
        byte_vector buf = {0};

        if (t0->fixed) {
                dump(&buf, "!");
        }

        switch (t0->type) {
        case TYPE_OBJECT:
                switch (t0->class->i) {
                case CLASS_TOP:     dump(&buf, "Any");    break;
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
                                        ShowType(v__(t0->args, i))
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
                dump(&buf, "Type[%s]", ShowType(t0->_type));
                break;
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        dump(
                                &buf,
                                (i == 0) ? "%s" : " | %s",
                                ShowType(v__(t0->types, i))
                        );

                }
                break;
        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        Type *t1 = v__(t0->types, i);
                        if (t1 != NULL && t1->type == TYPE_UNION) {
                                dump(
                                        &buf,
                                        (i == 0) ? "(%s)" : " & (%s)",
                                        ShowType(v__(t0->types, i))
                                );
                        } else {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : " & %s",
                                        ShowType(v__(t0->types, i))
                                );
                        }

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
                                                ShowType(c->t0),
                                                intern_entry(&xD.b_ops, c->op)->name,
                                                ShowType(c->t1),
                                                ShowType(c->rt)
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
                                        ShowType(p->type)
                                );
                        } else {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s: %s" : ", %s: %s",
                                        p->var->identifier,
                                        ShowType(p->type)
                                );
                        }
        
                }
                dump(&buf, ")");
                dump(&buf, " -> %s", ShowType(t0->rt));
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
                                                ShowType(v__(t0->types, i))
                                        );
                                } else {
                                        dump(
                                                &buf,
                                                (i == 0) ? "%s: %s" : ", %s: %s",
                                                v__(t0->names, i),
                                                ShowType(v__(t0->types, i))
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
                                        ShowType(v__(t0->types, i))
                                );
                        }
                        dump(&buf, ")");
                }
                break;

        case TYPE_VARIABLE:
                //var = scope_find_symbol(ty->tscope, t0->var);
                //if (t0->mark || var == NULL || var->type == t0 || var == t0->var) {
                //        dump(&buf, "%s", t0->var->identifier);
                //} else {
                //        t0->mark = true;
                //        dump(&buf, "%s%s%s", t0->var->identifier, var->fixed ? "==" : "=", ShowType(var->type));
                //        t0->mark = false;
                //}
                if (t0->val == NULL) {
                        dump(&buf, "%s", VarName(ty, t0->id));
                } else {
                        dump(&buf, "%s%s%s", VarName(ty, t0->id), t0->fixed ? "==" : "=", ShowType(t0->val));
                }
                if (vN(t0->args) > 0) {
                        dump(&buf, "[");
                        for (int i = 0; i < vN(t0->args); ++i) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        ShowType(v__(t0->args, i))
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
                dump(&buf, "%s", ShowType(t0->_type));
                break;

        case TYPE_NIL:
                dt -= 1;
                vvX(visiting);
                return sclone_malloc("nil");

        case TYPE_NONE:
                dt -= 1;
                vvX(visiting);
                return sclone_malloc("<none>");

        case TYPE_INTEGER:
                dump(&buf, "%"PRIiMAX, t0->z);
                break;
        }

        dt -= 1;

        vvX(visiting);

        return vN(buf) == 0 ? sclone_malloc("<?>") : buf.items;
}

Type *
type_unfixed(Ty *ty, Type *t0)
{
        Type *t;

        if (t0 != NULL && t0->fixed) {
                t = CloneType(ty, t0);
                t->fixed = true;
        } else {
                t = t0;
        }

        return t;
}

Type *
type_fixed(Ty *ty, Type *t0)
{
        Type *t;

        if (t0 != NULL && !t0->fixed) {
                t = CloneType(ty, t0);
                t->fixed = true;
        } else {
                t = t0;
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

        printf(
                "TypeOf2Op(%s):\n  %s\n  %s\n => %s\n",
                intern_entry(&xD.b_ops, op)->name,
                ShowType(t0),
                ShowType(t1),
                ShowType(t)
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
                return Propagate(ty, TypeArg(t0, 0));
        }

        if (ClassOfType(ty, t0) == CLASS_ITERABLE) {
                return Propagate(ty, TypeArg(t0, 0));
        }

        if (ClassOfType(ty, t0) == CLASS_ITER) {
                return Propagate(ty, TypeArg(t0, 0));
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
        LeaveScope();
}

void
type_function_fixup(Ty *ty, Type *t)
{
        if (t == NULL) {
                return;
        }

        ApplyConstraints(ty);

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
                        printf("%s :: %s :: %s\n", p->identifier, ShowType(p->type), ShowType(p0));
                        if (p->type == p0) {
                                printf("Keep %s :: %d\n", p->identifier, n);
                                *v_(t0->params, n) = p;
                                n += 1;
                        } else {
                                scope_insert(ty, GlobalTypeScope(ty), p)->type = p0;
                        }
                }

                t0->params.count = n;
        }
}

void
type_intersect(Ty *ty, Type **t0, Type *t1)
{
        printf("intersect()\n");
        printf("    %s\n", ShowType(*t0));
        printf("    %s\n", ShowType(t1));

        if (*t0 == NULL) {
                *t0 = type_unfixed(ty, t1);
                return;
        }

        if (t1 == NULL || (*t0)->fixed || type_check_x(ty, *t0, t1, CHECK_NOBIND)) {
                return;
        }

        if ((*t0)->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        if (type_check_x(ty, t1, v__((*t0)->types, i), CHECK_NOBIND)) {
                                return;
                        }
                }
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        if (type_check_x(ty, v__((*t0)->types, i), t1, CHECK_NOBIND)) {
                                *v_((*t0)->types, i) = t1;
                                return;
                        }
                }
                avP((*t0)->types, t1);
                return;
        }

        if (t1->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        type_intersect(ty, t0, v__(t1->types, i));
                }
                return;
        }

        // Float & (Int | String)

        Type *t2 = NewType(ty, TYPE_INTERSECT);
        avP(t2->types, *t0);
        avP(t2->types, t1);
        *t0 = t2;
}

void
type_subtract(Ty *ty, Type **t0, Type *t1)
{
        printf("subtract()\n");
        printf("    %s\n", ShowType(*t0));
        printf("    %s\n", ShowType(t1));

        if (IsBottom(*t0) || IsAny(*t0) || IsBottom(t1) || IsAny(t1)) {
                return;
        }

        if (!type_check_x(ty, *t0, t1, CHECK_NOBIND)) {
                return;
        }

        Type *t = *t0;

        switch ((*t0)->type) {
        case TYPE_UNION:
                t = CloneType(ty, *t0);
                CloneVec(t->types);
                v0(t->types);
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        Type *t2 = v__((*t0)->types, i);
                        if (!type_check_x(ty, t1, t2, CHECK_NOBIND)) {
                                type_subtract(ty, &t2, t1);
                                avP(t->types, t2);
                        }
                }
                break;

        case TYPE_INTERSECT:
                t = CloneType(ty, *t0);
                CloneVec(t->types);
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        type_subtract(ty, v_(t->types, i), t1);
                }
                break;
        }

        printf("subtract(   %s   ,   %s  )  =  %s\n", ShowType(*t0), ShowType(t1), ShowType(t));

        *t0 = t;

}

bool
TypeCheck(Ty *ty, Type *t0, Value const *v)
{
        printf("TypeCheck():\n");
        printf("    %s\n", VSC(v));
        printf("    %s\n", ShowType(t0));

        Value *var;

        if (IsBottom(t0)) {
                return true;
        }

        if (v->type == VALUE_NIL) {
                return type_check_x(ty, t0, NIL_TYPE, CHECK_NOBIND);
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
                printf("var(%d): %s = %s\n", t0->var->i, t0->var->identifier, VSC(var));
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

        case TYPE_FUNCTION:
                if (v->type == VALUE_FUNCTION) {
                        return type_check_x(ty, t0, type_of(v), CHECK_RUNTIME);
                }
                break;

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

void
types_init(Ty *ty)
{
        EnterScope();
}

/* vim: set sts=8 sw=8 expandtab: */
