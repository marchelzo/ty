#include "ty.h"
#include "types.h"
#include "class.h"
#include "intern.h"
#include "ast.h"
#include "compiler.h"
#include "operators.h"
#include "value.h"
#include "itable.h"

#include <libunwind.h>

enum { CHECK_BIND, CHECK_NOBIND, CHECK_RUNTIME };
enum { PROP_DEFAULT, PROP_FIX, PROP_UNFIX };

#undef NIL

#define ANY     TYPE_ANY
#define BOTTOM  BOTTOM_TYPE
#define UNKNOWN UNKNOWN_TYPE
#define NIL     NIL_TYPE

#define CloneVec(v) (                                  \
        (v).items = memcpy(                            \
                amA((v).capacity * sizeof *(v).items), \
                (v).items,                             \
                ((v).count * sizeof *(v).items)        \
        )                                              \
)

#define TypeError(...) do { ApplyConstraints(ty); CompileError(ty, __VA_ARGS__); } while (0)
#define ShowType(t) type_show(ty, (t))


// Walk the stack and return number of frames.
static inline int get_stack_depth(void) {
    unw_context_t ctx;
    unw_cursor_t cursor;
    int depth = 0;

    unw_getcontext(&ctx);
    unw_init_local(&cursor, &ctx);
    // unw_step returns >0 while there are frames
    while (unw_step(&cursor) > 0) {
        depth++;
    }
    return depth;
}


#if 1
#define TLOG(fmt, ...)                                                       \
    if (EnableLogging) {                                                     \
        int _d = get_stack_depth() - 6;                                      \
        if (_d < 0) _d = 0;                                                  \
        int _indent = _d * 4;                                                \
        fprintf(stderr, "%*s[%s] " fmt "\n", _indent, "", __func__ __VA_OPT__(,) ##__VA_ARGS__);  \
    } else if (0)
#else
#define TLOG(...)
#endif

#define XTLOG(fmt, ...)                                                      \
    if (1) {                                                                 \
        int _d = get_stack_depth() - 6;                                      \
        if (_d < 0) _d = 0;                                                  \
        int _indent = _d * 4;                                                \
        fprintf(stdout, "%*s[%s] " fmt "\n", _indent, "", __func__ __VA_OPT__(,) ##__VA_ARGS__);  \
    } else if (0)


static void *TVAR = (void *)&TVAR;
static void *HOLE = (void *)&HOLE;

static Expr *
FindMethod(Class const *c, char const *name);

static Type *
TypeOf2Op(Ty *ty, int op, Type *t0, Type *t1);

static void
BindChecked(Ty *ty, Type *t0, Type *t1);

static bool
BindConstraint(Ty *ty, Constraint const *c, bool check);

Type *
Inst(Ty *ty, Type *t0, U32Vector const *params, TypeVector const *args);

Type *
Inst1(Ty *ty, Type *t0);

static void
FoldConstraints(Ty *ty);

static void
ApplyConstraints(Ty *ty);

static Type *
ResolveAlias(Ty *ty, Type const *t0);

inline static Type *
ResolveVar(Type const *t0);

static bool
RefersTo(Type *t0, u32 id);

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

static char *
VarName(Ty *ty, u32 id);

static bool
SameType(Type const *t0, Type const *t1);

static bool
UnifyX(Ty *ty, Type *t0, Type *t1, bool super, bool check);

static void
Unify(Ty *ty, Type *t0, Type *t1, bool super);

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
Type *UNKNOWN_TYPE;
Type *TYPE_CLASS_;

static u32 NextID = 0;
static u32 CurrentLevel = 0;

static struct itable VarNameTable;
static int VarLetter = 'a';
static int VarNumber = 0;

#define EnterScope() do {                                  \
        dont_printf("===> ENTER\n");                            \
        xvP(ty->tcons, ((ConstraintVector){0}));           \
        ty->tenv = NewEnv(ty, ty->tenv);                   \
        ty->tscope = scope_new(ty, "", ty->tscope, false); \
        CurrentLevel += 1;                                 \
} while (0)

#define LeaveScope() do {                       \
        FoldConstraints(ty);                    \
        dont_printf("<=== LEAVE (%s)\n", __func__);  \
        ty->tscope = ty->tscope->parent;        \
        ty->tenv = ty->tenv->parent;            \
        CurrentLevel -= 1;                      \
} while (0)

static TypeEnv *
NewEnv(Ty *ty, TypeEnv *parent)
{
        TypeEnv *env = amA(sizeof *env);
        env->parent = parent;
        env->level = (parent != NULL) ? (parent->level +  1) : 0;
        itable_init(ty, &env->vars);
        return env;
}

static void
PutEnv(Ty *ty, TypeEnv *env, u32 id, Type *t0)
{
        itable_add(ty, &env->vars, id, PTR(t0));
}

static Type *
LookEnv(Ty *ty, TypeEnv *env, u32 id)
{
        Value const *v = itable_lookup(ty, &env->vars, id);
        return (v == NULL || v->type == VALUE_NIL) ? NULL : v->ptr;
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
IsUnboundVar(Type const *t0)
{
        return TypeType(t0) == TYPE_VARIABLE
            && t0->level != -1;
}

inline static bool
IsTVar(Type const *t0)
{
        return TypeType(t0) == TYPE_VARIABLE
            && t0->val == TVAR;
}

inline static bool
IsHole(Type const *t0)
{
        return TypeType(t0) == TYPE_VARIABLE
            && t0->val == HOLE;
}

inline static bool
IsBoundVar(Type const *t0)
{
        return TypeType(t0) == TYPE_VARIABLE
            && t0->level == -1;
}

inline static void
BindVar(Type *var, Type *val)
{
        TLOG("Bind(): %s := %s", ShowType(var), ShowType(val));
        if (var->val != TVAR) {
                var->val = val;
                var->level = -1;
        } else {
                TLOG("*** NOT BINDING ***");
        }
}


inline static bool
IsAny(Type const *t0)
{
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
IsFixed(Type const *t0)
{
        return t0 != NULL
            && t0->fixed;
}

inline static bool
IsUnknown(Type *t0)
{
        return IsBottom(t0) && IsFixed(t0);
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
        return t0;
}

static Type *
NewVarOf(Ty *ty, u32 id)
{
        Type *t0 = NewType(ty, TYPE_VARIABLE);
        t0->id = id;
        t0->level = CurrentLevel;
        return t0;
}

static Type *
NewHole(Ty *ty)
{
        Type *t0 = NewVar(ty);
        t0->val = HOLE;
        return t0;
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
        Type *p0 = NewVar(ty);
        avP(t0->params3, p0->id);
        return p0;
}

static Type *
AddScopedParam(Ty *ty, Type *t0)
{
        return AddParam(ty, t0);
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
                return vN(t0->params3);
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
        if (IsBoundVar(t0)) {
                return TypeArg(t0->val, i);
        }

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
ResolveVar(Type const *t0)
{
        while (IsBoundVar(t0)) {
                t0 = t0->val;
        }

        return t0;
}

inline static Type *
Resolve(Ty *ty, Type const *t0)
{
        for (;;) {
                if (IsBoundVar(t0)) {
                        t0 = t0->val;
                } else if (
                        TypeType(t0) == TYPE_ALIAS
                     && vN(t0->args) == vN(t0->params3)
                ) {
                        t0 = ResolveAlias(ty, t0);
                } else {
                        break;
                }
        }

        return (Type *)t0;
}

static bool
SameType(Type const *t0, Type const *t1)
{
        if (t0 == t1) {
                return true;
        }

        if (IsBoundVar(t0)) {
                return SameType(t0->val, t1);
        }

        if (IsBoundVar(t1)) {
                return SameType(t0, t1->val);
        }

        switch (PackTypes(t0, t1)) {
        case PAIR_OF(TYPE_VARIABLE):
                return t0->id == t1->id;

        case PAIR_OF(TYPE_OBJECT):
        case PAIR_OF(TYPE_CLASS):
                if (t0->class != t1->class || vN(t0->args) != vN(t1->args)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (!SameType(v__(t0->args, i), v__(t1->args, i))) {
                                return false;
                        }
                }
                return true;

        case PAIR_OF(TYPE_INTEGER):
                return t0->z == t1->z;

        case PAIR_OF(TYPE_BOTTOM):
        case PAIR_OF(TYPE_NIL):
                return true;

        case PAIR_OF(TYPE_UNION):
        case PAIR_OF(TYPE_INTERSECT):
                if (vN(t0->types) != vN(t1->types)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!SameType(v__(t0->types, i), v__(t1->types, i))) {
                                return false;
                        }
                }
                return true;

        case PAIR_OF(TYPE_TUPLE):
                if (vN(t0->types) != vN(t1->types)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->types); ++i) {
                        char *n0 = v__(t0->names, i);
                        char *n1 = v__(t1->names, i);
                        if (n0 != n1) {
                                if (n0 == NULL || n1 == NULL) {
                                        return false;
                                }
                                if (strcmp(n0, n1) != 0) {
                                        return false;
                                }
                        }
                        if (!SameType(v__(t0->types, i), v__(t1->types, i))) {
                                return false;
                        }
                }
                return true;

        case PAIR_OF(TYPE_FUNCTION):
                if (vN(t0->params3) != vN(t1->params3)) {
                        return false;
                }
                if (vN(t0->fun_params) != vN(t1->fun_params)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param const *p0 = v_(t0->fun_params, i);
                        Param const *p1 = v_(t1->fun_params, i);
                        if (p0->var != p1->var) {
                                if (p0->var == NULL || p1->var == NULL) {
                                        return false;
                                }
                                if (strcmp(p0->var->identifier, p1->var->identifier)) {
                                        return false;
                                }
                        }
                        if (
                                p0->rest != p1->rest
                             || p0->kws != p1->kws
                             || p0->required != p1->required
                        ) {
                                return false;
                        }
                        if (!SameType(p0->type, p1->type)) {
                                return false;
                        }
                }
                return SameType(t0->rt, t1->rt);
        }

        return false;
}

static Type *
Untagged(Type *t0, int tag)
{
        Type *t1 = NULL;
        Type *t2;

        t0 = Resolve(ty, t0);

        switch (TypeType(t0)) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t2 = Untagged(v__(t0->types, i), tag);
                        if (!IsBottom(t2)) {
                                unify2(ty, &t1, t2);
                        }
                }
                break;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t2 = Untagged(v__(t0->types, i), tag);
                        if (!IsBottom(t2)) {
                                type_intersect(ty, &t1, t2);
                        }
                }
                break;

        case TYPE_OBJECT:
                if (IsTagged(t0) && TagOf(t0) == tag) {
                        t1 = TypeArg(t0, 0);
                }
                break;
        }

        return (t1 == NULL) ? BOTTOM : t1;
}

static Type *
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
StrictClassOf(Type const *t0)
{
        if (TypeType(t0) == TYPE_INTEGER) {
                return CLASS_INT;
        }

        if (IsAny(t0)) {
                return CLASS_TOP;
        }

        if (TypeType(t0) != TYPE_OBJECT) {
                return CLASS_BOTTOM;
        }

        return t0->class->i;
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

        case TYPE_VARIABLE:
                return IsBoundVar(t0) ? ClassOfType(ty, t0->val) : CLASS_TOP;
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
                return t0;
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
RefersTo(Type *t0, u32 id)
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
                if (IsUnboundVar(t0)) {
                        ret = (t0->id == id);
                } else {
                        ret = RefersTo(t0->val, id);
                }
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (RefersTo(v__(t0->types, i), id)) {
                                ret = true;
                                break;
                        }
                }
                break;

        case TYPE_FUNCTION:
                if (RefersTo(t0->rt, id)) {
                        ret = true;
                        break;
                }
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        if (RefersTo(v_(t0->fun_params, i)->type, id)) {
                                ret = true;
                                break;
                        }
                }
                break;

        case TYPE_OBJECT:
        case TYPE_CLASS:
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (RefersTo(v__(t0->args, i), id)) {
                                ret = true;
                                break;
                        }
                }
                break;
        }

        vvX(visiting);

        return ret;
}

static bool
ContainsType(Type const *t0, Type const *t1)
{
        t0 = ResolveVar(t0);
        t1 = ResolveVar(t1);

        switch (TypeType(t0)) {
        case TYPE_UNION:
        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (SameType(ResolveVar(v__(t0->types, i)), t1)) {
                                return true;
                        }
                }
        }

        return false;
}

static Type *
Uniq(Ty *ty, Type *t0)
{
        int n;
        Type *t1 = t0;
        Type *t2;
        bool cloned = false;

        switch (TypeType(t0)) {
        case TYPE_UNION:
        case TYPE_INTERSECT:
                n = vN(t0->types);
                v0(t0->types);
                for (int i = 0; i < n; ++i) {
                        Type *t00 = v__(t0->types, i);
                        if (!ContainsType(t1, t00)) {
                                if (cloned) {
                                        vPx(t1->types, t00);
                                }
                        } else if (!cloned) {
                                t1 = CloneType(ty, t1);
                                CloneVec(t1->types);
                                cloned = true;
                        }
                        vPx(t0->types, t00);
                }
                break;

        case TYPE_VARIABLE:
                t2 = Uniq(ty, t0->val);
                if (t2 != t0->val) {
                        t1 = CloneType(ty, t1);
                        t1->val = t2;
                }
                break;
        }

        TLOG("Uniq(%s):   %s", ShowType(t0), ShowType(t1));

        return t1;
}

static bool
CollapseInts(Ty *ty, Type **t0)
{
        bool collapsed = false;

        while (IsBoundVar(*t0)) {
                t0 = &(*t0)->val;
        }

        for (int i = 0; i < UnionCount(*t0); ++i) {
                Type **t2 = UnionElemPtr(t0, i);
                if (StrictClassOf(*t2) == CLASS_INT) {
                        *t2 = TYPE_INT;
                        collapsed = true;
                }
        }

        if (collapsed) {
                *t0 = Uniq(ty, *t0);
        }

        return collapsed;
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
                        //avP(
                        //        t->params3,
                        //        t0->id
                        //);
                        avP(t->args, t0);
                }
        }

        TLOG("type_object(%s) = %s (narg=%d)", class->name, ShowType(t), (int)vN(t->args));

        return t;
}

Type *
type_variable(Ty *ty, Symbol *var)
{
        Type *t = NewVar(ty);
        t->val = TVAR;

        byte_vector name = {0};
        dump(&name, "%s", var->identifier);
        *itable_get(ty, &VarNameTable, t->id) = PTR(name.items);

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
                        t->params3,
                        t0->id
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
        
        Type *t0 = NewVar(ty);
        t0->val = TVAR;
        avP(t->params3, t0->id);

        class->type = t;
        class->object_type = NewType(ty, TYPE_OBJECT);
        class->object_type->class = class;
        avP(class->object_type->args, t0);

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
                                t->params3,
                                t0->id
                        );
                }
        }

        return t;
}

Type *
type_function(Ty *ty, Expr const *e)
{
        Type *t = NewType(ty, TYPE_FUNCTION);

        //fprintf(stderr, "================== %s ======================\n", e->name);

        if (e->return_type != NULL) {
                t->rt = type_fixed(ty, type_resolve(ty, e->return_type));
        } else {
                t->rt = NewHole(ty);
        }

        for (int i = 0; i < vN(e->type_params); ++i) {
                avP(t->params3, v__(e->type_params, i)->symbol->type->id);
        }

        if (e->class >= CLASS_OBJECT) {
                //avPv(t->params3, class_get_class(ty, e->class)->type->params3);
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
                                             || !type_check_x(
                                                        ty,
                                                        v__(e->constraints, i)->_type,
                                                        NIL_TYPE,
                                                        CHECK_NOBIND
                                                )
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
GatherFree(Ty *ty, Type *t0, U32Vector *freev)
{
        static int d = 0;

        //printf("%*sGatherFree(%s)\n", 4*d, "", ShowType(t0));

        t0 = Resolve(ty, t0);

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

        Type *t_ = t0;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        GatherFree(ty, t0->val, freev);
                } else if (t0->level >= CurrentLevel) { // || IsTVar(t0)) {
                        avP(*freev, t0->id);
                }
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        GatherFree(ty, v__(t0->types, i), freev);
                }
                break;

        case TYPE_OBJECT:
                for (int i = 0; i < vN(t0->args); ++i) {
                        GatherFree(ty, v__(t0->args, i), freev);
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_ALIAS:
                if (vN(t0->args) == vN(t0->params3)) {
                        GatherFree(ty, ResolveAlias(ty, t0), freev);
                }
                break;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        GatherFree(ty, p->type, freev);
                }
                GatherFree(ty, t0->rt, freev);
                break;
        }

        d -= 1;

        //printf("%*sGatherFree(%s) => %s\n", d*4, "", ShowType(t_), ShowType(t0));

        vvX(visiting);
}

static Type *
PropagateX(Ty *ty, Type *t0, bool drill, int mode)
{
        static int d = 0;

        dont_printf("%*sPropagate(%s)\n", 4*d, "", ShowType(t0));

        if (drill) {
                t0 = Resolve(ty, t0);
        }

        switch (mode) {
        case PROP_FIX:   t0 = type_fixed(ty, t0);   break;
        case PROP_UNFIX: t0 = type_unfixed(ty, t0); break;
        case PROP_DEFAULT:                          break;
        default:
                UNREACHABLE();
        }

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

        Type *t1;
        Type *t2;
        bool cloned = false;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        t1 = PropagateX(ty, t0->val, drill, mode);
                        if (t1 != t0->val) {
                                t0 = CloneType(ty, t0);
                        }
                        t0->val = t1;
                } else {
                        t1 = LookEnv(ty, ty->tenv, t0->id);
                        t0 = (t1 != NULL) ? t1 : t0;
                }
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        t2 = PropagateX(ty, t1, drill, mode);
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
                        t2 = PropagateX(ty, t1, drill, mode);
                        if (t2 != t1 && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->args);
                                cloned = true;
                        }
                        *v_(t0->args, i) = t2;
                }
                for (int i = vN(t0->args); i < vN(t0->params3); ++i) {
                        t1 = LookEnv(ty, ty->tenv, v__(t0->params3, i));
                        avP(t0->args, (t1 != NULL) ? t1 : NULL);
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_ALIAS:
                for (int i = 0; i < vN(t0->args); ++i) {
                        t1 = v__(t0->args, i);
                        t2 = PropagateX(ty, t1, drill, mode);
                        if (t2 != t1 && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->args);
                                cloned = true;
                        }
                        *v_(t0->args, i) = t2;
                }
                t1 = Inst(ty, t0->_type, &t0->params3, &t0->args);
                if (t1 != t0->_type && !cloned) {
                        t0 = CloneType(ty, t0);
                }
                t0->_type = t1;
                break;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        t1 = PropagateX(ty, p->type, drill, mode);
                        if (t1 != p->type && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->fun_params);
                                cloned = true;
                        }
                        *v_(t0->fun_params, i) = *p;
                        v_(t0->fun_params, i)->type = t1;
                }
                t1 = PropagateX(ty, t0->rt, drill, mode);
                if (t1 != t0->rt && !cloned) {
                        t0 = CloneType(ty, t0);
                }
                t0->rt = t1;
                break;
        }

        d -= 1;
        vvX(visiting);

        return t0;
}

static Type *
Propagate(Ty *ty, Type *t0)
{
        Type *t1 = PropagateX(ty, t0, false, PROP_DEFAULT);
        TLOG("Propagate(): %s", ShowType(t0));
        TLOG("             %s", ShowType(t1));
        return t1;
}

inline static bool
ContainsID(U32Vector const *vars, u32 id)
{
        for (int i = 0; i < vN(*vars); ++i) {
                if (v__(*vars, i) == id) {
                        return true;
                }
        }

        return false;
}

static bool
Occurs(Ty *ty, Type *t0, u32 id, int level)
{
        static int d = 0;

        dont_printf("%*sOccurs(%s)\n", 4*d, "", ShowType(t0));

        if (t0 == NULL) {
                return false;
        }

        static TypeVector visiting;
        if (already_visiting(&visiting, t0)) {
                return false;
        } else {
                xvP(visiting, t0);
        }

        bool ret = false;

        d += 1;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        ret = Occurs(ty, t0->val, id, level);
                } else if (!IsTVar(t0)) {
                        t0->level = min(t0->level, level);
                        ret = t0->id == id;
                }
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (Occurs(ty, v__(t0->types, i), id, level)) {
                                ret = true;
                                break;
                        }
                }
                break;

        case TYPE_OBJECT:
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (Occurs(ty, v__(t0->args, i), id, level)) {
                                ret = true;
                                break;
                        }
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_ALIAS:
                if (vN(t0->args) == vN(t0->params3)) {
                        t0 = ResolveAlias(ty, t0);
                }
                break;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (Occurs(ty, p->type, id, level)) {
                                ret = true;
                                break;
                        }
                }
                if (Occurs(ty, t0->rt, id, level)) {
                        ret = true;
                }
        }

        d -= 1;

        vvX(visiting);

        return ret;
}

static Type *
Generalize(Ty *ty, Type *t0)
{
        Type *t1 = t0;
        U32Vector bound = {0};

        switch (TypeType(t0)) {
        case TYPE_FUNCTION:
                GatherFree(ty, t0, &bound);
                for (int i = 0; i < vN(t0->params3); ++i) {
                        if (RefersTo(t0, v__(t0->params3, i))) {
                                avP(bound, v__(t0->params3, i));
                        }
                }
                dont_printf("Free(%s): ", ShowType(t0));
                for (int i = 0; i < vN(bound); ++i) {
                        if (i > 0) dont_printf(", ");
                        dont_printf("%s", VarName(ty, v__(bound, i)));
                }
                dont_printf("\n");
                if (true || vN(bound) != 0) {
                        t1 = CloneType(ty, t0);
                        v00(t1->params3);
                        for (int i = 0; i < vN(bound); ++i) {
                                if (!ContainsID(&t1->params3, v__(bound, i))) {
                                        avP(t1->params3, v__(bound, i));
                                }
                        }
                }
                break;
        }

        TLOG("Generalize(): %s   --->    %s", ShowType(t0), ShowType(t1));

        return t1;
}

static bool
UnifyXD(Ty *ty, Type *t0, Type *t1, bool super, bool check, bool soft)
{
        Type *t2;

        static int d = 0;
        static TypeVector visiting;

        if (check) {
                TLOG("Unify(%s, %s):  [ %s ]   with   [ %s ]", super ? "super" : "sub", soft ? "soft" : "hard", ShowType(t0), ShowType(t1));
                //printf("%*sUnify(%s, %s):\n    %*s%s\n    %*s%s\n\n", 4*d, "", super ? "super" : "sub", soft ? "soft" : "hard", 4*d, "", ShowType(t0), 4*d, "", ShowType(t1));
        } else {
                TLOG("TryUnify(%s, %s):  [ %s ]   with   [ %s ]", super ? "super" : "sub", soft ? "soft" : "hard", ShowType(t0), ShowType(t1));
                //printf("%*sTryUnify(%s, %s):\n    %*s%s\n    %*s%s\n\n", 4*d, "", super ? "super" : "sub", soft ? "soft" : "hard", 4*d, "", ShowType(t0), 4*d, "", ShowType(t1));
        }

        if (already_visiting(&visiting, t0)) {
                return true;
        }

        xvP(visiting, t0);

        d += 1;

        if (d > 14) {
                *(char *)0 = 0;
        }

        for (;;) {
                if (TypeType(t0) == TYPE_ALIAS) {
                        t0 = ResolveAlias(ty, t0);
                } else if (
                        IsBoundVar(t0)
                     && (IsBoundVar(t0->val) || t0->fixed)
                ) {
                        t0 = t0->val;
                } else {
                        break;
                }
        }

        t1 = Resolve(ty, t1);

        if (SameType(t0, t1)) {
                d -= 1;
                vvX(visiting);
                TLOG("=> UnifyXD() short circuit:  %s   ---   %s   are the same type", ShowType(t0), ShowType(t1));
                return true;
        }

        if (
                IsUnboundVar(t0)
             && IsUnboundVar(t1)
             && t0->id == t1->id
        ) {
                d -= 1;
                vvX(visiting);
                TLOG("=> UnifyXD() short circuit:  %s   ---   %s  are the same unbound variable", ShowType(t0), ShowType(t1));
                return true;
        }

        if (IsUnboundVar(t0) && !IsTVar(t0) && (!soft || IsHole(t0) || IsUnknown(t1))) {
                if (Occurs(ty, t1, t0->id, t0->level)) {
                        BindVar(t0, BOTTOM);
                        //TypeError(
                        //        "can't unify:\n  %s\n  %s\n",
                        //        ShowType(t0),
                        //        ShowType(t1)
                        //);
                } else {
                        BindVar(t0, type_really_unfixed(ty, t1));
                }
        } else if (false && IsHole(t1)) {
                if (Occurs(ty, t0, t1->id, t1->level)) {
                        BindVar(t1, BOTTOM);
                } else {
                        BindVar(t1, t0);
                }
                d -= 1;
                vvX(visiting);
                return true;
        }

        if (IsBottom(t0) || (IsBottom(t1) && !IsFixed(t1))) {
                d -= 1;
                vvX(visiting);
                return true;
        }

        if (
                IsTagged(t0)
             && IsTagged(t1)
             && TagOf(t0) == TagOf(t1)
        ) {
                TLOG("Merge:  %s   <--->   %s", ShowType(t0), ShowType(t1));
                UnifyXD(ty, v_(t0->args, 0), v__(t1->args, 0), super, check, soft);
                TLOG("After: %s", ShowType(t0));
        }

        if (TypeType(t0) == TYPE_UNION) {
                if (super) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                if (UnifyXD(ty, v__(t0->types, i), t1, super, false, soft)) {
                                        d -= 1;
                                        vvX(visiting);
                                        return true;
                                }
                        }
                } else {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                if (!UnifyXD(ty, v__(t0->types, i), t1, super, false, soft)) {
                                        d -= 1;
                                        vvX(visiting);
                                        return false;
                                }
                        }
                }
        }

        if (IsBoundVar(t0)) {
                UnifyXD(ty, t0->val, t1, super, false, soft);
                if (super) {
                        if (!type_check_x(ty, t0->val, t1, CHECK_NOBIND || IsUnknown(t1))) {
                                unify2(ty, &t0->val, t1);
                        }
                } else {
                        if (!type_check_x(ty, t1, t0->val, CHECK_NOBIND) || IsUnknown(t1)) {
                                type_intersect(ty, &t0->val, t1);
                        }
                }
        }

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                for (int i = 0; i < ArgCount(t0) && i < ArgCount(t1); ++i) {
                        UnifyXD(ty, TypeArg(t0, i), TypeArg(t1, i), super, check, soft);
                }
                if (t0->class->i >= CLASS_PRIMITIVE && t0->class->def != NULL) {
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
                                UnifyXD(ty, t, u, super, check, soft);
                        }
                        for (int i = 0; i < vN(def->methods); ++i) {
                                // TODO
                        }
                }
                break;

        case TYPE_TUPLE:
                if (TypeType(t1) == TYPE_TUPLE) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                char const *name = v__(t0->names, i);
                                t2 = (name != NULL)
                                   ? RecordField(ty, t1, name)
                                   : RecordElem(t1, i);
                                if (t2 != NULL) {
                                        UnifyXD(ty, v__(t0->types, i), t2, super, check, soft);
                                }
                        }
                        for (int i = 0; i < vN(t1->types); ++i) {
                                char const *name = v__(t1->names, i);
                                t2 = (name != NULL)
                                   ? RecordField(ty, t0, name)
                                   : RecordElem(t0, i);
                                if (t2 != NULL) {
                                        UnifyXD(ty, t2, v__(t1->types, i), super, check, soft);
                                }
                        }
                } else if (TypeType(t1) == TYPE_OBJECT) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                char const *name = v__(t0->names, i);
                                t2 = (name != NULL)
                                   ? type_member_access_t(ty, t1, name)
                                   : NULL;
                                if (t2 != NULL) {
                                        UnifyXD(ty, v__(t0->types, i), t2, super, check, soft);
                                }
                        }
                }
                break;

        case TYPE_FUNCTION:
                if (TypeType(t1) == TYPE_CLASS) {
                        t1 = ClassFunctionType(ty, t1);
                }
                if (TypeType(t1) == TYPE_FUNCTION) {
                        for (int i = 0; i < vN(t0->fun_params); ++i) {
                                Param const *p0 = v_(t0->fun_params, i);
                                Param const *p1 = (vN(t1->fun_params) > i) ? v_(t1->fun_params, i) : NULL;
                                if (
                                        (p0->kws || p0->rest)
                                     || ((p1 != NULL) && (p1->kws || p1->rest))
                                ) {
                                        continue;
                                }
                                //   (Int -> Any)   (Object -> String)
                                Type *t2 = (p1 == NULL) ? NIL_TYPE : p1->type;
                                UnifyXD(ty, p0->type, t2, !super, false, soft);
                                UnifyXD(ty, t2, p0->type, super, check, soft);
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
                                UnifyXD(ty, p1->type, t2, super, check, soft);
                        }
                        for (int i = 0; i < vN(t0->constraints); ++i) {
                                BindConstraint(ty, v_(t0->constraints, i), super);
                        }
                        for (int i = 0; i < vN(t1->constraints); ++i) {
                                BindConstraint(ty, v_(t1->constraints, i), super);
                        }
                        UnifyXD(ty, t0->rt, t1->rt, super, check, soft);
                }
                break;
        }

        if (false && (IsTVar(t0) || IsTVar(t1))) {
                d -= 1;
                vvX(visiting);
                TLOG("=> UnifyXD() force success: one of [ %s ]   [ %s ] is a TVar", ShowType(t0), ShowType(t1));
                return true;
        }

        bool unified = type_check_x(ty, super ? t0 : t1, super ? t1 : t0, CHECK_NOBIND);

        if (check && !unified) {
                TypeError(
                        "type mismatch: have %s%s%s where %s%s%s is expected",
                        TERM(93),
                        super ? ShowType(t1) : ShowType(t0),
                        TERM(0),
                        TERM(93),
                        super ? ShowType(t0) : ShowType(t1),
                        TERM(0)
                );
        }

        d -= 1;
        vvX(visiting);

        return unified;
}

static bool
UnifyX(Ty *ty, Type *t0, Type *t1, bool super, bool check)
{
        TLOG("UnifyX():");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s\n", ShowType(t1));

        return UnifyXD(ty, t0, t1, super, false, true)
            || UnifyXD(ty, t0, t1, super, check, false);
}

static void
Unify(Ty *ty, Type *t0, Type *t1, bool super)
{
        UnifyX(ty, t0, t1, super, true);

}

static bool
BindConstraint(Ty *ty, Constraint const *c, bool check)
{
        Type *t0;
        Type *t1;
        Type *t2;

        switch (c->type) {
        case TC_2OP:
                break;
                t0 = Propagate(ty, c->t0);
                t1 = Propagate(ty, c->t1);
                t2 = Propagate(ty, c->rt);
                dont_printf(
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
                        return true;
                }
                break;

        case TC_EQ:
                //t0 = Propagate(ty, c->t0);
                //t1 = Propagate(ty, c->t1);
                //BindVars(ty, t1, t0, false);
                //BindVars(ty, t0, t1, check);
                UnifyX(ty, c->t0, c->t1, true, false);
                UnifyX(ty, c->t1, c->t0, false, true);
                break;

        }

        return true;
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
ApplyConstraintsX(Ty *ty, ConstraintVector *cons)
{
        dont_printf("ApplyConstraints():\n");
        for (int i = 0; i < vN(*cons); ++i) {
                Constraint const *c = v_(*cons, i);
                switch (c->type) {
                case TC_EQ:
                        dont_printf("============    %s  =  %s\n", ShowType(c->t0), ShowType(c->t1));
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

        v0(*cons);
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
ResolveAlias(Ty *ty, Type const *t0)
{
        if (
                TypeType(t0) == TYPE_ALIAS
             && vN(t0->args) == vN(t0->params3)
        ) {
                return Inst(ty, t0->_type, &t0->params3, &t0->args);
        } else {
                return (Type *)t0;
        }

}

static Type *
TagFunctionType(Ty *ty, Type *t0)
{
        if (t0->ft != NULL) {
                return t0->ft;
        }

        Type *f0 = NewType(ty, TYPE_FUNCTION);
        Type *v0 = NewVar(ty);

        avP(f0->params3, v0->id);
        avP(f0->fun_params, PARAM(NULL, v0, true));

        f0->rt = NewType(ty, TYPE_OBJECT);
        f0->rt->class = t0->class;
        avP(f0->rt->args, v0);

        t0->ft = f0;

        return f0;
}

static Type *
ClassFunctionType(Ty *ty, Type *t0)
{
        Type *t1 = Inst(ty, t0->class->object_type, &t0->class->type->params3, NULL);
        //Type *t1 = t0->class->object_type;

        //if (vN(t1->args) != vN(t0->class->type->params3)) {
        //        CloneVec(t1->args);
        //        while (vN(t1->args) != vN(t0->class->type->params3)) {
        //                avP(t1->args, NewVarOf(ty, v__(t0->class->type->params3, vN(t1->args))));
        //        }
        //}

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
        //return Generalize(ty, t2);
}

static bool
CheckCall(Ty *ty, expression_vector const *args, Type *t0)
{
        Type *t1;
        Type *t2;
        Expr *init;

        dont_printf("CheckCall(%s)\n", ShowType(t0));
        for (int i = 0; i < vN(*args); ++i) {
                dont_printf("    %s\n", ShowType(v__(*args, i)->_type));
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
InferCall(Ty *ty, expression_vector const *args, Type *t0)
{
        Type *t1;

        dont_printf("InferCall(%s)\n", ShowType(t0));
        for (int i = 0; i < vN(*args); ++i) {
                dont_printf("    %s\n", ShowType(v__(*args, i)->_type));
        }

        if (t0 == NULL) {
                return NULL;
        }

        switch (t0->type) {
        case TYPE_FUNCTION:
                for (int i = 0; i < vN(*args) && i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (p->rest || p->kws) {
                                break;
                        }
                        Type *p0 = v_(t0->fun_params, i)->type;
                        //Type *a0 = Inst1(ty, v__(*args, i)->_type);
                        Type *a0 = v__(*args, i)->_type;
                        UnifyX(ty, p0, a0, true, false);
                        ApplyConstraints(ty);
                        UnifyX(ty, a0, p0, false, true);
                }
                for (int i = vN(*args); i < vN(t0->fun_params); ++i) {
                        Param const *p = v_(t0->fun_params, i);
                        if (p->rest || p->kws) {
                                break;
                        }
                        if (p->required) {
                                if (p->var != NULL) {
                                        TypeError(
                                                "missing required argument for parameter %s%s%s of type `%s`",
                                                TERM(93), p->var->identifier, TERM(0),
                                                ShowType(v_(t0->fun_params, i)->type)
                                        );
                                } else {
                                        TypeError(
                                                "missing required argument for parameter of type `%s`",
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
                return InferCall(ty, args, ClassFunctionType(ty, t0));

        case TYPE_TAG:
                return InferCall(ty, args, TagFunctionType(ty, t0));

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        if (CheckCall(ty, args, t1)) {
                                return InferCall(ty, args, t1);
                        }
                }
        }

        return NULL;
}

static Type *
type_call_t(Ty *ty, Expr const *e, Type *t0)
{
        if (IsBottom(t0)) {
                return t0;
        }

        if (IsNil(t0)) {
                return NIL;
        }

        Type *t;
        Type *t1;
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
                return InferCall(ty, args, Inst1(ty, t0));

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
                if (IsBoundVar(t0)) {
                        return type_call_t(ty, e, t0->val);
                } else {
                        t1 = NewType(ty, TYPE_FUNCTION);
                        t1->rt = NewVar(ty);
                        for (int i = 0; i < vN(*args); ++i) {
                                Type *p0 = NewVar(ty);
                                avP(t1->fun_params, PARAM(NULL, p0, true));
                                avP(t1->params3, p0->id);
                        }
                        //t1 = Inst1(ty, Generalize(ty, t1));
                        for (int i = 0; i < vN(*args); ++i) {
                                Unify(ty, v_(t1->fun_params, i)->type, v__(*args, i)->_type, true);
                        }
                        BindVar(t0, t1);
                        //return Generalize(ty, t1->rt);
                        return t1->rt;
                }
        }

        return NULL;
}

Type *
type_call(Ty *ty, Expr const *e)
{
        //EnterScope();
        Type *t0 = type_call_t(ty, e, e->function->_type);
        dont_printf("type_call()\n");
        dont_printf("    >>> %s\n", show_expr(e));
        dont_printf("    %s\n", ShowType(t0));
        //printf("SolveCall(%s, %s) = %s\n", show_expr(e), ShowType(t0), ShowType(t));
        //LeaveScope();
        ApplyConstraints(ty);
        return Generalize(ty, t0);
}

Type *
type_match(Ty *ty, Expr const *e)
{
        Type *t0 = NULL;
        Type *s0 = NULL;

        for (int i = 0; i < e->patterns.count; ++i) {
                Expr *p = v__(e->patterns, i);
                Type *s00;
                if (p->type == EXPRESSION_LIST) {
                        s0 = NULL;
                        for (int j = 0; j < vN(p->es); ++j) {
                                Type *s000 = NewHole(ty);
                                type_assign(ty, v__(p->es, j), s00, false);
                                unify2(ty, &s00, s000);
                        }
                } else {
                        s00 = NewHole(ty);
                        type_assign(ty, p, s00, false);
                }
                unify2(ty, &s0, s00);
        }

        UnifyX(ty, e->subject->_type, s0, true, false);
        UnifyX(ty, s0, e->subject->_type, false, true);

        for (int i = 0; i < e->patterns.count; ++i) {
                TLOG("match |= %s", ShowType(v__(e->thens, i)->_type));
                unify2(ty, &t0, v__(e->thens, i)->_type);
        }

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
Inst(Ty *ty, Type *t0, U32Vector const *params, TypeVector const *args)
{
        TLOG("Inst(): %s", ShowType(t0));

        bool skip = true;
        for (int i = 0; i < vN(*params); ++i) {
                if (RefersTo(t0, v__(*params, i))) {
                        skip = false;
                        break;
                }
        }

        if (skip) {
                return t0;
        }
        
        TypeVector vars = {0};

        if (args == NULL) {
                for (int i = 0; i < vN(*params); ++i) {
                        avP(vars, NewHole(ty));
                }
                args = &vars;
        }

        TypeEnv *save = ty->tenv;
        ty->tenv = NewEnv(ty, NULL);

        for (int i = 0; i < vN(*params) && i < vN(*args); ++i) {
                TLOG("  %s := %s", VarName(ty, v__(*params, i)), ShowType(v__(*args, i)));
                PutEnv(ty, ty->tenv, v__(*params, i), v__(*args, i));
        }

        t0 = Propagate(ty, t0);

        ty->tenv = save;

        return t0;
}

Type *
Inst1(Ty *ty, Type *t0)
{
        Type *t1 = t0;

        if (TypeType(t0) == TYPE_FUNCTION) {
                t1 = Inst(ty, t0, &t0->params3, NULL);
                if (t1 == t0) {
                        t1 = CloneType(ty, t1);
                }
                v00(t1->params3);
        } else if (TypeType(t0) == TYPE_OBJECT) {
                t1 = Inst(ty, t0, &t0->class->type->params3, NULL);
                if (t1 == t0) {
                        t1 = CloneType(ty, t1);
                }
                v00(t1->params3);
        }

        TLOG("Inst1():");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s\n", ShowType(t1));

        return t1;
}

Type *
SolveMemberAccess(Ty *ty, Type *t0, Type *t1)
{
        if (TypeType(t0) != TYPE_OBJECT || IsBottom(t1)) {
                return t1;
        }

        t0 = Resolve(ty, t0);

        Type *t = t1;
        Class *c = t0->class;
        ClassDefinition *def = &c->def->class;

        for (int i = 0; i < vN(def->traits); ++i) {
                Expr *trait = v__(def->traits, i);
                if (trait->type == EXPRESSION_SUBSCRIPT) {
                        TLOG("SolveMemberAccess(): apply trait: %s", trait->container->identifier);
                } else {
                        TLOG("SolveMemberAccess(): apply trait: %s", trait->identifier);
                }
                Type *tr0 = Inst(
                        ty,
                        type_resolve(ty, trait),
                        &c->type->params3,
                        &t0->args
                );
                if (tr0 != NULL && tr0->class != NULL) {
                        t = Inst(
                                ty,
                                t,
                                &tr0->class->type->params3,
                                &tr0->args
                        );
                }
        }

        t = Inst(ty, t, &c->type->params3, &t0->args);
        t = Inst1(ty, t);

        TLOG("SolveMemberAccess():");
        TLOG("    %s", ShowType(t1));
        TLOG("    %s\n", ShowType(t));

        return t;
}

Type *
type_member_access_t_(Ty *ty, Type *t0, char const *name)
{
        TLOG("member_access(%s, %s)", ShowType(t0), name);

        if (IsAny(t0) || IsBottom(t0)) {
                return BOTTOM;
        }

        if (IsNil(t0)) {
                return NIL;
        }

        t0 = Resolve(ty, t0);

        int class;
        Class *c;
        Value *field;
        Expr *f;

        Type *t1 = NULL;

        switch (t0->type) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify(ty, &t1, type_member_access_t_(ty, v__(t0->types, i), name));
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
                                t1 = v__(t0->types, i);
                                break;
                        }
                }
                return t1;

        case TYPE_OBJECT:
                class = ClassOfType(ty, t0);
                field = (class >= CLASS_PRIMITIVE)
                      ? class_lookup_field_i(ty, class, M_ID(name))
                      : NULL;
                if (field != NULL) {
                        t1 = (field->extra != NULL)
                           ? type_resolve(ty, field->extra)
                           : ((Expr *)field->ptr)->_type;
                } else {
                        c = class_get_class(ty, class);
                        f = FindMethod(c, name);
                        if (f != NULL) {
                                t1 = f->_type;
                        }
                }
                return SolveMemberAccess(ty, t0, t1);

        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        return type_member_access_t_(ty, t0->val, name);
                } else {
                        t1 = NewType(ty, TYPE_TUPLE);
                        avP(t1->names, name);
                        avP(t1->types, NewVar(ty));
                        BindVar(t0, t1);
                        return *vvL(t1->types);
                }
        }
        
        return t1;
}

Type *
type_member_access_t(Ty *ty, Type *t0, char const *name)
{
        Type *t1 = type_member_access_t_(ty, t0, name);
        TLOG("MemberAccess(%s):", name);
        TLOG("  t0:  %s", ShowType(t0));
        TLOG("  t1:  %s\n", ShowType(t1));
        return t1;
}

Type *
type_member_access(Ty *ty, Expr const *e)
{
        //EnterScope();

        Type *t0 = e->type == EXPRESSION_DYN_MEMBER_ACCESS
                 ? BOTTOM //UnionOf(ty, e->object->_type)
                 : type_member_access_t(ty, e->object->_type, e->member_name);

        //LeaveScope();

        //return Generalize(ty, t0);
        return t0;
}

Type *
type_method_call_t(Ty *ty, Expr const *e, Type *t0, char const *name)
{
        t0 = Resolve(ty, t0);

        if (IsNil(t0)) {
                return NIL;
        }

        if (IsBottom(t0)) {
                return t0;
        }

        if (e->type == EXPRESSION_DYN_METHOD_CALL) {
                return BOTTOM;
        }

        Class *c;
        Expr *f;
        Type *t;

        switch (t0->type) {
        case TYPE_OBJECT:
        case TYPE_VARIABLE:
        case TYPE_TUPLE:
                t = SolveMemberAccess(ty, t0, type_member_access_t(ty, t0, name));
                t = SolveMemberAccess(ty, t0, type_call_t(ty, e, t));
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
        //EnterScope();

        Type *t1 = type_method_call_t(ty, &(Expr){ .type = EXPRESSION_METHOD_CALL }, t0, name);
        //ApplyConstraints(ty);
        //t1 = Propagate(ty, t1);
        dont_printf("type_method_call_name()\n");
        dont_printf("    %s\n", name);
        dont_printf("    %s\n", ShowType(t0));
        dont_printf("    %s\n", ShowType(t1));

        //LeaveScope();

        //return Generalize(ty, t1);
        return t1;
}

Type *
type_method_call(Ty *ty, Expr const *e)
{
        //EnterScope();

        //Type *t0 = type_method_call_t(ty, e, Inst1(ty, e->object->_type), e->method_name);
        Type *t0 = type_method_call_t(ty, e, e->object->_type, e->method_name);
        //ApplyConstraints(ty);
        //t0 = Propagate(ty, t0);
        dont_printf("type_method_call(%s)\n", e->method_name);
        dont_printf("    >>> %s\n", show_expr(e));
        dont_printf("    %s\n", ShowType(e->object->_type));
        dont_printf("    %s\n", ShowType(t0));

        //LeaveScope();

        //return Generalize(ty, t0);
        return t0;
}

Type *
type_tagged(Ty *ty, int tag, Type *t0)
{
        Type *t1 = NewType(ty, TYPE_OBJECT);

        t1->class = tags_get_class(ty, tag);
        avP(t1->args, type_unfixed(ty, t0));

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

        t0 = Resolve(ty, t0);
        t1 = Resolve(ty, t1);

        if (IsBottom(t0) || IsBottom(t1)) {
                return BOTTOM;
        }

        switch (t0->type) {
        case TYPE_OBJECT:
                switch (t0->class->i) {
                case CLASS_ARRAY:  t = TypeArg(t0, 0); break;
                case CLASS_DICT:   t = TypeArg(t0, 1); break;
                case CLASS_STRING: t = TYPE_STRING;    break;
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

        dont_printf("subscript(%s):\n", ShowType(t1));
        dont_printf("  %s\n", ShowType(t0));
        dont_printf("  %s\n", ShowType(t));

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
                        Type *m0 = SolveMemberAccess(ty, t0, m->_type);
                        return type_check_x(ty, m0, t1, mode);
                }
        }

        return false;
}

static int d = 0;
//#define print(fmt, ...) dont_printf("%*s" fmt "\n", d*4, "", __VA_ARGS__ + 0)
#define print(...) 0

bool
type_check_x_(Ty *ty, Type *t0, Type *t1, int mode)
{
        t0 = Resolve(ty, t0);
        t1 = Resolve(ty, t1);

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

        if (IsUnboundVar(t0) && IsUnboundVar(t1)) {
                return t0->id == t1->id;
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

        if (t1->type == TYPE_OBJECT && t1->class->def != NULL) {
                ClassDefinition *def = &t1->class->def->class;
                for (int i = 0; i < vN(def->traits); ++i) {
                        if (
                                type_check_x(
                                        ty,
                                        t0,
                                        SolveMemberAccess(ty, t1, type_resolve(ty, v__(def->traits, i))),
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
                                SolveMemberAccess(ty, t1, type_resolve(ty, def->super)),
                                mode
                        )
                ) {
                        return true;
                }
        }
        
        if (t0->type == TYPE_TUPLE) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        char const *name = v__(t0->names, i);
                        if (
                                name == NULL
                              ? !type_check_x(
                                      ty,
                                      v__(t0->types, i),
                                      RecordElem(t1, i),
                                      CHECK_NOBIND
                                )
                              : !type_check_x(
                                        ty, v__(t0->types, i),
                                        RecordField(ty, t1, name),
                                        CHECK_NOBIND
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
                              ? !check_entry(ty, t0, i, v__(t1->types, i), mode)
                              : !check_field(ty, t0, name, v__(t1->types, i), mode)
                        ) {
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
                                        mode
                                )
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

        if (t0->type == TYPE_FUNCTION && t1->type == TYPE_TAG) {
                t1 = TagFunctionType(ty, t1);
        }

        if (t1->type == TYPE_FUNCTION && t0->type == TYPE_TAG) {
                t0 = TagFunctionType(ty, t0);
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
                        Type *p0 = pp0->type;
                        Type *p1 = pp1->type;
                        UnifyX(ty, p0, p1, true, false);
                        UnifyX(ty, p1, p0, false, false);
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
                //ApplyConstraints(ty);
                Type *r0 = t0->rt;
                Type *r1 = t1->rt;
                UnifyX(ty, r1, r0, true, false);
                UnifyX(ty, r0, r1, false, false);
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
        TLOG("type_check(%s):", mode == CHECK_BIND ? "bind" : "");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s", ShowType(t1));
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
        TLOG(" => %s\n", b ? "true" : "false");
        return b;
}


bool
type_check(Ty *ty, Type *t0, Type *t1)
{
        return type_check_x(ty, t0, t1, CHECK_NOBIND);
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

        v00(t->args);

        Type *t1 = NewVar(ty);
        Type *t2 = NewVar(ty);

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

        v00(t->args);

        Type *t1 = NewVar(ty);

        if (t0 != NULL && vN(ty->tcons) != 0) {
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
                unify2(ty, &t0, v__(e->elements, i)->_type);
        }

        CollapseInts(ty, &t0);

        t0 = ArrayOf(ty, Relax(t0));

        ApplyConstraints(ty);

        return t0;
}

void
type_assign(Ty *ty, Expr *e, Type *t0, bool fixed)
{
        if (t0 == NULL) {
                t0 = BOTTOM;
        }

        TLOG("assign(%s)", fixed ? "fixed" : "");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s\n", show_expr(e));

        Type *t1;

        //t0 = Resolve(ty, t0);

        if (TypeType(t0) == TYPE_UNION) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        type_assign(ty, e, v__(t0->types, i), false);
                }
                for (int i = 0; i < vN(t0->types); ++i) {
                        type_assign(ty, e, v__(t0->types, i), fixed);
                }
                return;
        }

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_RESOURCE_BINDING:
                if (!e->symbol->fixed) {
                        if (t0 == NULL) {
                                t0 = NewVar(ty);
                        }
                        TLOG(
                                "type_assign(): %s : %s |= %s",
                                e->symbol->identifier,
                                ShowType(e->symbol->type),
                                ShowType(t0)
                        );
                        unify(ty, &e->_type, t0);
                        unify_(ty, &e->symbol->type, t0, false);
                        e->symbol->fixed |= fixed;
                        TLOG(
                                "type_assign(): %s |= %s    --->    %s",
                                e->symbol->identifier,
                                ShowType(t0),
                                ShowType(e->symbol->type)
                        );
                } else if (
                        !UnifyXD(ty, t0, e->symbol->type, false, false, false)
                ) {
                        TypeError(
                                "can't assign `%s` to %s%s%s which has type `%s`",
                                ShowType(t0),
                                TERM(93), e->identifier, TERM(0),
                                ShowType(e->symbol->type)
                        );
                }
                break;
        case EXPRESSION_TAG_APPLICATION:
                for (int i = 0; i < UnionCount(t0); ++i) {
                        Type *t1 = UnionElem(t0, i);
                        TLOG("type_assign(0): t1 :: %s", ShowType(t1));
                        t1 = Resolve(ty, t1);
                        TLOG("type_assign(1): t1 :: %s", ShowType(t1));
                        if (IsUnboundVar(t1)) {
                                Type *t2 = NewHole(ty);
                                Type *t3 = type_tagged(ty, e->symbol->tag, t2);
                                BindVar(t0, t3);
                                t1 = t3;
                        }
                        type_assign(ty, e->tagged, Untagged(t1, e->symbol->tag), fixed);
                        //if (IsTagged(t1) && TagOf(t1) == e->symbol->tag) {
                        //        TLOG(
                        //                "type_assign(): %s |= %s",
                        //                ShowType(e->tagged->_type),
                        //                ShowType(t1)
                        //        );
                        //        type_assign(ty, e->tagged, TypeArg(t1, 0), fixed);
                        //}
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
                if (IsUnboundVar(t0) && !IsTVar(t0)) {
                        t1 = NewType(ty, TYPE_TUPLE);
                        for (int i = 0; i < vN(e->es); ++i) {
                                char const *name = v__(e->names, i);
                                avP(t1->names, name);
                                avP(t1->types, NewVar(ty));
                        }
                        BindVar(t0, t1);
                        t0 = t1;
                }
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
                        break;
                }
                break;
        case EXPRESSION_LIST:
                type_assign(ty, v__(e->es, 0), t0, fixed);
                break;
        }
}

Type *
type_inst(Ty *ty, Type const *t0)
{
        return Inst1(ty, (Type *)t0);
}

Type *
type_drill(Ty *ty, Type const *t0)
{
        return PropagateX(ty, (Type *)t0, true, PROP_DEFAULT);
}

Type *
type_var(Ty *ty)
{
        return NewVar(ty);
}

Type *
type_resolve(Ty *ty, Expr const *e)
{
        Type *t0;
        Type *t1;
        Type *t2;
        Symbol *var;

        if (e == NULL) {
                return NULL;
        }

        dont_printf("Resolve(): %s\n", show_expr(e));

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (e->symbol == NULL) {
                        t0 = NULL;
                } else if (e->symbol->class != -1) {
                        t0 = NewType(ty, TYPE_OBJECT);
                        t0->class = class_get_class(ty, e->symbol->class);
                } else if (e->symbol->tag != -1) {
                        t0 = e->symbol->type;
                } else if (!IsBottom(e->symbol->type) && !IsHole(e->symbol->type)) {
                        t0 = e->symbol->type;
                } else {
                        var = scope_find_symbol(ty->tscope, e->symbol);
                        if (var != NULL) {
                                t0 = var->type;
                        } else if (e->symbol->type_var) {
                                return e->symbol->type;
                                t0 = LookEnv(ty, ty->tenv, e->symbol->type->id);
                                if (t0 == NULL) {
                                        t0 = NewVarOf(ty, e->symbol->type->id);
                                        PutEnv(ty, ty->tenv, e->symbol->type->id, t0);
                                }
                        } else {
                                t0 = ANY;
                        }
                }
                dont_printf("resolve(): %s -> %s\n", e->identifier, ShowType(t0));
                return t0;

        case EXPRESSION_MATCH_ANY:
                return type_fixed(ty, UNKNOWN);

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
                dont_printf("resolve_subscript(): -> %s\n", ShowType(t0));
                return t0;

        case EXPRESSION_TUPLE:
                t0 = NewType(ty, TYPE_TUPLE);
                for (int i = 0; i < vN(e->es); ++i) {
                        avP(t0->names, v__(e->names, i));
                        avP(t0->types, type_resolve(ty, v__(e->es, i)));
                }
                return t0;

        case EXPRESSION_BIT_OR:
                t1 = type_unfixed(ty, type_resolve(ty, e->left));
                t2 = type_unfixed(ty, type_resolve(ty, e->right));
                if (type_check(ty, t1, t2)) {
                        return t1;
                }
                if (type_check(ty, t2, t1)) {
                        return t2;
                }
                t0 = NewType(ty, TYPE_UNION);
                avP(t0->types, t1);
                avP(t0->types, t2);
                return t0;

        case EXPRESSION_BIT_AND:
                t1 = type_unfixed(ty, type_resolve(ty, e->left));
                t2 = type_unfixed(ty, type_resolve(ty, e->right));
                if (type_check(ty, t1, t2)) {
                        return t2;
                }
                if (type_check(ty, t2, t1)) {
                        return t1;
                }
                t0 = NewType(ty, TYPE_INTERSECT);
                avP(t0->types, t1);
                avP(t0->types, t2);
                return t0;

        case EXPRESSION_PREFIX_QUESTION:
                t0 = type_resolve(ty, e->operand);
                unify(ty, &t0, NIL_TYPE);
                return t0;

        case EXPRESSION_FUNCTION:
                return NULL;

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
                t0 = NewType(ty, TYPE_OBJECT);
                t0->class = class_get_class(ty, CLASS_ARRAY);
                avP(
                        t0->args,
                        vN(e->elements) == 0 ? NULL : type_resolve(
                                ty,
                                v__(e->elements, 0)
                        )
                );
                return t0;

        case EXPRESSION_NIL:
                return NIL;

        case EXPRESSION_INTEGER:
                return type_integer(ty, e->integer);
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
                unify2(ty, t0, t1);
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
        TLOG("unify2()");
        TLOG("    %s", ShowType(*t0));
        TLOG("    %s\n", ShowType(t1));

        if (IsUnknown(Resolve(ty, t1))) {
                *t0 = UNKNOWN;
                return;
        }

        if (t1 == NULL) {
                t1 = BOTTOM;
        }

        if (*t0 == NULL || IsAny(t1) || *t0 == NONE_TYPE) {
                *t0 = type_really_unfixed(ty, t1);
                return;
        }

        if (IsUnknown(*t0)) {
                return;
        }

        if (
                UnifyXD(ty, *t0, t1, true, false, true)
             || UnifyXD(ty, t1, *t0, false, false, true)
        ) {
                TLOG("=> unify2() early exit: UnifyXD() succeeded");
                TLOG("=> [ %s ]    [ %s ]", ShowType(*t0), ShowType(t1));
                return;
        }

        if (
                ClassOfType(ty, t1) == CLASS_INT
             && CollapseInts(ty, t0)
        ) {
                return;
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
        } else if ((*t0)->type == TYPE_UNION && !(*t0)->fixed) {
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        if (try_coalesce(ty, v_((*t0)->types, i), t1)) {
                                return;
                        }
                }
                avP((*t0)->types, t1);
        } else if (!IsFixed(*t0)) {
                Type *union_ = NewType(ty, TYPE_UNION);
                avP(union_->types, *t0);
                avP(union_->types, t1);
                *t0 = union_;
        }

        if (!type_check(ty, *t0, t1)) {
                TypeError("type error: `%s` != `%s`", ShowType(*t0), ShowType(t1));
        }

}

static void
unify_(Ty *ty, Type **t0, Type *t1, bool fixed)
{
        TLOG("unify()");
        TLOG("    %s", ShowType(*t0));
        TLOG("    %s\n", ShowType(t1));

        if (t1 == NULL) {
                t1 = BOTTOM;
        }

        if (*t0 == NULL || *t0 == BOTTOM || IsAny(t1) || IsUnknown(t1) || *t0 == NONE_TYPE) {
                *t0 = type_really_unfixed(ty, t1);
                return;
        }

        if (type_check_x(ty, *t0, t1, CHECK_NOBIND)) {
                return;
        }

        if (!fixed && !(*t0)->fixed) {
                UnifyX(ty, *t0, t1, true, false);
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

        if (dt > 128) { *(char *)0 = 0; }

        while (IsBoundVar(t0)) {
                t0 = t0->val;
        }

        static TypeVector visiting;
        if (already_visiting(&visiting, t0)) {
                dt -= 1;
                return sclone_malloc("...");
        } else {
                xvP(visiting, t0);
        }

        byte_vector buf = {0};

        if (IsFixed(t0)) {
                //dump(&buf, "!");
        }

        if (IsBottom(t0)) {
                dt -= 1;
                vvX(visiting);
                dump(&buf, "%s", "🔴");
        }

        switch (TypeType(t0)) {
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
                dump(&buf, "Class[%s]", t0->class->name != NULL ? t0->class->name : "?");
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
                if (vN(t0->params3) > 0) {
                        dump(&buf, "[");
                        for (int i = 0; i < vN(t0->params3); ++i) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        VarName(ty, v__(t0->params3, i))
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
                if (IsUnboundVar(t0)) {
                        dump(&buf, "%s", VarName(ty, t0->id));
                } else {
                        //dump(&buf, "%s", type_show(ty, t0->val));
                        dump(&buf, "%s%s(%s)", VarName(ty, t0->id), t0->fixed ? "==" : "=", ShowType(t0->val));
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
                dump(&buf, "%s", t0->name);
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

        if (!IsUnknown(t0) && IsFixed(t0)) {
                t = CloneType(ty, t0);
                t->fixed = false;
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

Type *
type_really_unfixed(Ty *ty, Type *t0)
{
        return PropagateX(ty, t0, false, PROP_UNFIX);
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
                ShowType(t0),
                ShowType(t1),
                ShowType(t)
        );

        return t;
}

Type *
type_binary_op(Ty *ty, Expr const *e)
{
        Type *t0 = Resolve(ty, e->left->_type);
        Type *t1 = Resolve(ty, e->right->_type);

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

        if (
                TyCompilerState(ty)->func != NULL
             && (
                        IsUnboundVar(t0)
                     || IsUnboundVar(t1)
                )
        ) {
                Type *ft = TyCompilerState(ty)->func->_type;
                Type *t2 = NewVar(ty);
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
        Type *t1 = ArrayOf(ty, t0);
        ApplyConstraints(ty);
        return Generalize(ty, t1);
        //return t0;
}

Type *
type_iterable_type(Ty *ty, Type *t0)
{
        Type *t1 = NULL;
        Type *t2;

        t0 = Resolve(ty, t0);

        if (IsUnboundVar(t0)) {
                t1 = NewVar(ty);
                t2 = NewType(ty, TYPE_OBJECT);
                t2->class = class_get_class(ty, CLASS_ITERABLE);
                avP(t2->args, t1);
                BindVar(t0, t2);
                //return Generalize(ty, t1);
                return t1;
        }

        Class *c;
        ClassDefinition *def;

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                c = t0->class;
                def = (c->def == NULL) ? NULL : &c->def->class;
                for (int i = 0; def != NULL && i < vN(def->traits); ++i) {
                        Expr *t = v__(def->traits, i);
                        if (t->type != EXPRESSION_SUBSCRIPT) {
                                continue;
                        }
                        if (
                                TypeType(t->container->_type) != TYPE_CLASS
                             || t->container->_type->class->i != CLASS_ITERABLE
                        ) {
                                continue;
                        }
                        t1 = SolveMemberAccess(ty, t0, type_resolve(ty, t->subscript));
                        break;
                }
                if (t1 != NULL) {
                        break;
                }
                switch (ClassOfType(ty, t0)) {
                case CLASS_ARRAY:
                case CLASS_DICT:
                case CLASS_ITERABLE:
                case CLASS_ITER:
                        t1 = TypeArg(t0, 0);
                        break;
                default:
                        t1 = BOTTOM;
                }
                break;

        case TYPE_UNION:
                t1 = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify2(ty, &t1, type_iterable_type(ty, v__(t0->types, i)));
                }
                break;
        }

        dont_printf("iterable_type(%s):   %s\n", ShowType(t0), ShowType(t1));

        return t1;
}

void
type_scope_push(Ty *ty, bool fun)
{
        //ty->tscope = scope_new(ty, "", ty->tscope, fun);
        EnterScope();
}

void
type_scope_pop(Ty *ty)
{
        LeaveScope();
}

Type *
type_function_fixup(Ty *ty, Type *t)
{
        ApplyConstraints(ty);

        for (int i = 0; i < IntersectCount(t); ++i) {
                Type *t0 = IntersectElem(t, i);

                if (TypeType(t0) != TYPE_FUNCTION) {
                        TypeError("Bro? %s", ShowType(t0));
                }

                for (int i = 0; i < vN(t0->fun_params); ++i) {
                        Param *p = v_(t0->fun_params, i);
                        p->type = type_fixed(ty, p->type);
                }

                t0->rt = type_fixed(ty, t0->rt);
        }

        return Generalize(ty, t);
}

void
type_intersect(Ty *ty, Type **t0, Type *t1)
{
        dont_printf("intersect()\n");
        dont_printf("    %s\n", ShowType(*t0));
        dont_printf("    %s\n", ShowType(t1));

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

        Type *t2 = NewType(ty, TYPE_INTERSECT);
        avP(t2->types, *t0);
        avP(t2->types, t1);
        *t0 = t2;
}

void
type_subtract(Ty *ty, Type **t0, Type *t1)
{
        dont_printf("subtract()\n");
        dont_printf("    %s\n", ShowType(*t0));
        dont_printf("    %s\n", ShowType(t1));

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
                v00(t->types);
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
                for (int i = 0; i < vN(t->types); ++i) {
                        type_subtract(ty, v_(t->types, i), t1);
                }
                break;
        }

        dont_printf("subtract(   %s   ,   %s  )  =  %s\n", ShowType(*t0), ShowType(t1), ShowType(t));

        *t0 = t;
}

bool
TypeCheck(Ty *ty, Type *t0, Value const *v)
{
        dont_printf("TypeCheck():\n");
        dont_printf("    %s\n", VSC(v));
        dont_printf("    %s\n", ShowType(t0));

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
                if (IsBoundVar(t0)) {
                        return TypeCheck(ty, t0->val, v);
                } else {
                        return true;
                }

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
                return CALLABLE(*v)
                    || class_lookup_method_i(ty, ClassOf(v), NAMES.call) != NULL;

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
