#include "ty.h"
#include "types.h"
#include "class.h"
#include "intern.h"
#include "ast.h"
#include "compiler.h"

#undef NIL

#define ANY TYPE_ANY
#define NIL NIL_TYPE

static Expr *
FindMethod(Class const *c, char const *name);

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
TypeEntry(Type *t0, int i)
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

        if (e->return_type != NULL) {
                t->rt = type_resolve(ty, e->return_type);
        }

        for (int i = 0; i < vN(e->type_params); ++i) {
                avP(t->params, v__(e->type_params, i)->symbol);
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
        dont_printf("Propagate(%s)\n", type_show(ty, t0));

        if (t0 == NULL) {
                return NULL;
        }

        Symbol *var;
        Type *t1;
        Type *t2;
        bool cloned = false;

        Type *t_ = t0;

        switch (t0->type) {
        case TYPE_VARIABLE:
                var = scope_find_symbol(ty->tscope, t0->var);
                if (var == NULL) {
                        break;
                }
                t1 = t0;
                t0 = CloneType(ty, var->type);
                for (int i = 0; i < vN(t1->args); ++i) {
                        avP(t0->args, Propagate(ty, v__(t1->args, i)));
                }
                break;

        case TYPE_UNION:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        t2 = Propagate(ty, t1);
                        if (t2 != t1 && !cloned) {
                                t0 = CloneType(ty, t0);
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
                break;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                }
                t1 = Propagate(ty, t0->rt);
                if (t1 != t0->rt && !cloned) {
                        t0 = CloneType(ty, t0);
                }
                t0->rt = t1;
                break;
        }

        dont_printf("Propagate(%s) => %s\n", type_show(ty, t_), type_show(ty, t0));

        return t0;
}

static void
BindVars(Ty *ty, Type *t0, Type *t1)
{
        dont_printf("BindVar():\n  %s\n  %s\n", type_show(ty, t0), type_show(ty, t1));

        if (t0 == NULL) {
                return;
        }

        Symbol *var;
        Type *t2;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (vN(t0->args) == 0) {
                        var = scope_find_symbol(ty->tscope, t0->var);
                        if (var == NULL) {
                                var = scope_insert(ty, ty->tscope, t0->var);
                                var->type = CloneType(ty, t1);
                                if (var->type != NULL) {
                                        v0(var->type->args);
                                }
                                var->type = Relax(var->type);
                                dont_printf("BindVar(): %s := %s\n", var->identifier, type_show(ty, var->type));
                        } else {
                                unify(ty, &var->type, t1);
                        }
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
                        if (var == NULL) {
                                var = scope_insert(ty, ty->tscope, t0->var);
                                var->type = NULL;
                        }
                        if (extra > 0) {
                                t2 = CloneType(ty, t1);
                                v0(t2->args);
                                avPvn(t2->args, t1->args, extra);
                                t1 = t2;
                        }
                        unify(ty, &var->type, Relax(t1));
                        dont_printf("BindVar(): %s := %s\n", var->identifier, type_show(ty, var->type));
                }
                break;

        case TYPE_OBJECT:
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
                break;

        case TYPE_UNION:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                }
                break;

        case TYPE_FUNCTION:
                break;
        }
}

static Type *
SolveCall(Ty *ty, Expr const *e, Type *t0)
{
        Type *t;

        Type *t1;
        Expr *init;

        dont_printf("SolveCall(%s, %s)\n", show_expr(e), type_show(ty, t0));

        ty->tscope = scope_new(ty, "", ty->tscope, true);

        switch (t0->type) {
        case TYPE_FUNCTION:
                for (int i = 0; i < vN(e->args) && i < vN(t0->fun_params); ++i) {
                        BindVars(ty, v_(t0->fun_params, i)->var->type, v__(e->args, i)->_type);
                }

                dont_printf("rt = %s\n", type_show(ty, t0->rt));
                t = Propagate(ty, t0->rt);
                dont_printf("rt after propagate = %s\n", type_show(ty, t));
                break;

        case TYPE_CLASS:
                init = FindMethod(t0->class, "init");
                if (init == NULL) {
                        break;
                }

                t1 = init->_type;
                if (t1 == NULL) {
                        // FIXME
                        dont_printf("%s %s.init(): null\n", type_show(ty, t0), t0->class->name);
                        t = t0;
                        break;
                }

                for (int i = 0; i < vN(e->args) && i < vN(t1->fun_params); ++i) {
                        BindVars(ty, v_(t1->fun_params, i)->var->type, v__(e->args, i)->_type);
                }

                dont_printf("rt = %s\n", type_show(ty, t0->class->object_type));
                t = Propagate(ty, t0->class->object_type);
                dont_printf("rt after propagate = %s\n", type_show(ty, t));
                break;
        }

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

        switch (t0->type) {
        case TYPE_FUNCTION:
                return SolveCall(ty, e, t0);

        case TYPE_CLASS:
                return SolveCall(ty, e, t0);

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
        }

        return NULL;
}

Type *
type_call(Ty *ty, Expr const *e)
{
        return type_call_t(ty, e, e->function->_type);
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

        ty->tscope = scope_new(ty, "", ty->tscope, true);

        for (int i = 0; i < vN(t0->args) && i < vN(t0->params); ++i) {
                var = scope_insert(
                        ty,
                        ty->tscope,
                        v__(t0->params, i)
                );
                var->type = v__(t0->args, i);
                dont_printf("SolveMemberAccess(): %s := %s  (args=%zu, params=%zu)\n", var->identifier, type_show(ty, var->type), vN(t0->args), vN(t0->params));
        }

        t = Propagate(ty, t1);
        dont_printf("SolveMemberAccess(%s): %s\n", type_show(ty, t1), type_show(ty, t));

        ty->tscope = ty->tscope->parent;

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
        }

        return NULL;
}

Type *
type_member_access(Ty *ty, Expr const *e)
{
        return e->type == EXPRESSION_DYN_MEMBER_ACCESS
             ? UnionOf(ty, e->object->_type)
             : type_member_access_t(ty, e->object->_type, e->member_name);
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
                c = t0->class;
                f = FindMethod(c, name);
                return ReturnType(f);
        
        case TYPE_CLASS:
                c = t0->class;
                f = FindStatic(c, name);
                return ReturnType(f);

        case TYPE_TUPLE:
                t = type_member_access_t(ty, t0, name);
                return (t == NULL || t->type != TYPE_FUNCTION)
                     ? NULL
                     : t->rt;

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
type_method_call(Ty *ty, Expr const *e)
{
        return type_method_call_t(ty, e, e->object->_type, e->method_name);
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
                     ? TypeEntry(t0, t1->z)
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
check_entry(Ty *ty, Type *t0, int i, Type *t1)
{
        if (NullOrAny(t0)) {
                return false;
        }

        switch (t0->type) {
        case TYPE_UNION:
                for (int ii = 0; ii < vN(t0->types); ++ii) {
                        if (!check_entry(ty, v__(t0->types, ii), i, t1)) {
                                return false;
                        }
                }
                return true;

        case TYPE_TUPLE:
                return vN(t0->types) > i
                    && type_check(ty, v__(t0->types, i), t1);
        }

        return false;
}

static bool
check_field(Ty *ty, Type *t0, char const *name, Type *t1)
{
        if (NullOrAny(t0)) {
                return false;
        }

        Value const *field;

        switch (t0->type) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!check_field(ty, v__(t0->types, i), name, t1)) {
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
                                return type_check(ty, v__(t0->types, i), t1);
                        }
                }
                return false;

        case TYPE_OBJECT:
                field = class_lookup_field_i(ty, t0->class->i, M_ID(name));
                if (field != NULL) {
                        return type_check(
                                ty,
                                (
                                        (field->extra != NULL)
                                      ? type_resolve(ty, field->extra)
                                      : ((Expr *)field->ptr)->_type
                                ),
                                t1
                        );
                }
        }

        return false;
}

static int d = 0;
//#define print(fmt, ...) dont_printf("%*s" fmt "\n", d*4, "", __VA_ARGS__ + 0)
#define print(...) 0

bool
type_check_(Ty *ty, Type *t0, Type *t1)
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

        if (t0->type == TYPE_UNION && t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (!type_check(ty, t0, v__(t1->types, i))) {
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
                        if (type_check(ty, v__(t0->types, i), t1)) {
                                return true;
                        }
                }
                return false;
        }

        if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (!type_check(ty, t0, v__(t1->types, i))) {
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
                                !type_check(
                                        ty,
                                        v__(t0->args, i),
                                        TypeArg(t1, i)
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
                              ? !check_entry(ty, t0, i, v__(t1->types, i))
                              : !check_field(ty, t0, name, v__(t1->types, i))
                        ) {
                                return false;
                        }
                }
                return true;
        }

        return false;
}

bool
type_check(Ty *ty, Type *t0, Type *t1)
{
        print("%s : %s", type_show(ty, t1), type_show(ty, t0));
        d += 1;
        bool b = type_check_(ty, t0, t1);
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

Type *
type_array(Ty *ty, Expr const *e)
{
        Type *t0 = NULL;

        for (int i = 0; i < vN(e->elements); ++i) {
                unify(ty, &t0, v__(e->elements, i)->_type);
        }

        Type *t = type_object(ty, class_get_class(ty, CLASS_ARRAY));
        avP(t->args, Relax(t0));

        return t;
}

void
type_assign(Ty *ty, Expr *e, Type *t0)
{
        if (t0 == NULL) {
                return;
        }

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_RESOURCE_BINDING:
                unify(ty, &e->_type, t0);
                unify(ty, &e->symbol->type, t0);
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
        }
}

Type *
type_resolve(Ty *ty, Expr const *e)
{
        Type *t0;
        Symbol *var;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (e->symbol->class != -1) {
                        t0 = class_get_class(ty, e->symbol->class)->object_type;
                } else {
                        var = scope_find_symbol(ty->tscope, e->symbol);
                        t0 = (var != NULL) ? var->type : e->symbol->type;
                }
                dont_printf("resolve(): %s -> %s\n", e->identifier, type_show(ty, t0));
                return t0;

        case EXPRESSION_SUBSCRIPT:
                t0 = CloneType(ty, type_resolve(ty, e->container));
                avP(t0->args, type_resolve(ty, e->subscript));
                dont_printf("resolve_subscript(): -> %s\n", type_show(ty, t0));
                return t0;

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

        case EXPRESSION_NIL:
                return NIL;
        }

        dont_printf("resolve() failed: %s\n", show_expr(e));

        return NULL;
}

void
unify(Ty *ty, Type **t0, Type *t1)
{
        if (*t0 == NULL || NullOrAny(t1)) {
                *t0 = t1;
                return;
        }

        if (type_check(ty, *t0, t1)) {
                return;
        }

        if ((*t0)->type == TYPE_INTEGER && t1->type == TYPE_INTEGER) {
                *t0 = TYPE_INT;
        } else if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        unify(ty, t0, v__(t1->types, i));
                }
        } else if ((*t0)->type == TYPE_UNION) {
                avP((*t0)->types, t1);
        } else {
                Type *union_ = NewType(ty, TYPE_UNION);
                avP(union_->types, *t0);
                avP(union_->types, t1);
                *t0 = union_;
        }
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

char const *
type_show(Ty *ty, Type *t0)
{
        if (NullOrAny(t0)) {
                return "Any";
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
        case TYPE_FUNCTION:
                dump(&buf, "(");
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        dump(
                                &buf,
                                (i == 0) ? "%s: %s" : ", %s: %s",
                                p->var->identifier,
                                type_show(ty, p->type)
                        );
                }
                dump(&buf, ") -> %s", type_show(ty, t0->rt));
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
                if (var == NULL || var->type == t0) {
                        dump(&buf, "%s", t0->var->identifier);
                } else {
                        dump(&buf, "%s=%s", t0->var->identifier, type_show(ty, var->type));
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

        case TYPE_NIL:
                return "nil";

        case TYPE_INTEGER:
                dump(&buf, "%"PRIiMAX, t0->z);
                break;
        }

        return buf.items;
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
