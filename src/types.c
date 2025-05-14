#include "ty.h"
#include "types.h"
#include "class.h"
#include "intern.h"
#include "ast.h"
#include "compiler.h"
#include "operators.h"
#include "value.h"
#include "itable.h"
#include "str.h"
#include "blob.h"
#include "array.h"
#include "dict.h"

#include <libunwind.h>

typedef struct {
        TypeVector id0;
        TypeVector id1;
        vec(bool) memo;
} TypeMemo;

#define ENFORCE (!AllowErrors)
#define ENABLED (CheckConstraints)

enum { PROP_DEFAULT, PROP_FIX, PROP_UNFIX };

#define ANY     TYPE_ANY
#define BOTTOM  BOTTOM_TYPE
#define UNKNOWN UNKNOWN_TYPE

#define CloneVec(v) (                                  \
        (v).items = memcpy(                            \
                amA((v).capacity * sizeof *(v).items), \
                (v).items,                             \
                ((v).count * sizeof *(v).items)        \
        )                                              \
)

#define TypeError(...) do { CompileError(ty, __VA_ARGS__); } while (0)
#define ShowType(t) type_show(ty, (t))

#define NewObject(c, ...) ((NewObject)(ty, c, __VA_ARGS__ __VA_OPT__(,) NULL))
#define NewRecord(...) ((NewRecord)(ty, __VA_ARGS__ __VA_OPT__(,) NULL))
#define NewFunction(...) ((NewFunction)(ty, __VA_ARGS__ __VA_OPT__(,) NULL))

#if 0
static inline int get_stack_depth(void) {
    unw_context_t ctx;
    unw_cursor_t cursor;
    int depth = 0;

    unw_getcontext(&ctx);
    unw_init_local(&cursor, &ctx);
    while (unw_step(&cursor) > 0) {
        depth++;
    }
    return depth;
}

#define TLOG(fmt, ...)                                                       \
    if (EnableLogging > 8) {                                                 \
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


#define XXTLOG(fmt, ...) (EnableLogging > 0 && printf("[%2d] " fmt "\n", CurrentLevel __VA_OPT__(,) __VA_ARGS__))
#define XXXTLOG(fmt, ...) (printf("[%2d] " fmt "\n", CurrentLevel __VA_OPT__(,) __VA_ARGS__))
#define DPRINT(cond, fmt, ...) ((cond) && EnableLogging > 0 && printf("%*s" fmt "\n", 4*d, "" __VA_OPT__(,) __VA_ARGS__))
#define XDPRINT(cond, fmt, ...) ((cond) && printf("%*s" fmt "\n", 4*d, "" __VA_OPT__(,) __VA_ARGS__))

static void *TVAR = (void *)&TVAR;
static void *HOLE = (void *)&HOLE;
static void *REPLACE = (void *)&REPLACE;
static void *NAMED = (void *)&NAMED;
static void *OPTIONAL = (void *)&OPTIONAL;

static Type ERROR = { .type = TYPE_ERROR, .fixed = true };

static Value STATIC_NIL = NIL;

enum { LOW_FUEL = 5, MAX_FUEL = 999999 };
static int FUEL = MAX_FUEL;

static bool
IsSolved(Type const *t0);

static Expr *
FindMethod(Class const *c, char const *name);

static Type *
TypeOf2Op(Ty *ty, int op, Type *t0, Type *t1);

static void
BindChecked(Ty *ty, Type *t0, Type *t1);

static bool
BindConstraint(Ty *ty, Constraint const *c, bool check);

static void
fixup(Ty *ty, Type *t0);

static Type *
Inst(Ty *ty, Type *t0, U32Vector const *params, TypeVector const *args);

static Type *
Inst1(Ty *ty, Type *t0);

static void
FoldConstraints(Ty *ty);

static void
ApplyConstraints(Ty *ty);

static Type *
ResolveAlias(Ty *ty, Type const *t0);

inline static Type *
ResolveVar(Type const *t0);

inline static Type *
NthType(Type const *t0, int i);

static Type *
ListItem(Ty *ty, Type const *t0, int idx, Type const *alt);

static Type *
SliceType(Ty *ty, Type const *t0, int i, int j, int k);

static bool
RefersTo(Type *t0, u32 id);

static Type *
Uniq(Ty *ty, Type *t0);

static Type *
SolveMemberAccess(Ty *ty, Type const *t0, Type const *t1);

bool
type_check_x(Ty *ty, Type *t0, Type *t1, bool need);

static bool
type_check_shallow(Ty *ty, Type *t0, Type *t1);

static bool
type_check2(Ty *ty, Type *t0, Type *t1, bool need);

Value *
vm_local(Ty *ty, int i);

static void
unify_(Ty *ty, Type **t0, Type *t1, bool fixed);

static bool
unify2_(Ty *ty, Type **t0, Type *t1, bool check);

static Type *
ArrayOf(Ty *ty, Type *t0);

static Type *
DictOf(Ty *ty, Type *k0, Type *v0);

static Type *
(NewObject)(Ty *ty, int class, ...);

static Type *
(NewRecord)(Ty *ty, ...);

static Type *
ClassFunctionType(Ty *ty, Type *t0);

static Type *
TagFunctionType(Ty *ty, Type *t0);

static char *
VarName(Ty *ty, u32 id);

static bool
SameType(Type const *t0, Type const *t1);

static bool
UnifyX(Ty *ty, Type *t0, Type *t1, bool super, bool check);

static void
Unify(Ty *ty, Type *t0, Type *t1, bool super);

static Type *
MakeConcrete(Ty *ty, Type *t0, TypeVector *refs);

Type *TYPE_INT;
Type *TYPE_FLOAT;
Type *TYPE_BOOL;
Type *TYPE_STRING;
Type *TYPE_REGEX;
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

static U32Vector FixedTypeVars;

inline static bool
FuelCheck(void)
{
        if (FUEL <= 0) {
                EnableLogging = 0;
                TypeError("ran out of fuel :(");
                return false;
        }

        FUEL -= 1;

        if (FUEL == LOW_FUEL) {
                EnableLogging = 1;
        }

        return FUEL > 0;
}

#define EnterScope() do {                                  \
        xvP(ty->tcons, ((ConstraintVector){0}));           \
        ty->tscope = scope_new(ty, "", ty->tscope, false); \
        CurrentLevel += 1;                                 \
} while (0)

#define LeaveScope() do {                       \
        FoldConstraints(ty);                    \
        ty->tscope = ty->tscope->parent;        \
        CurrentLevel -= 1;                      \
} while (0)

inline static char *
mkcstr(Ty *ty, Value const *v)
{
        if (v != NULL && v->type == VALUE_STRING) {
                char *s = amA(v->bytes + 1);

                memcpy(s, v->string, v->bytes);
                s[v->bytes] = '\0';

                return s;
        } else {
                return NULL;
        }
}

static TypeEnv *
NewEnv(Ty *ty, TypeEnv *parent)
{
        TypeEnv *env = amA(sizeof *env);
        env->parent = parent;
        env->level = (parent != NULL) ? (parent->level +  1) : 0;
        itable_init(ty, &env->vars);
        return env;
}

static Type *
PutEnv(Ty *ty, TypeEnv *env, u32 id, Type *t0)
{
        itable_add(ty, &env->vars, id, PTR(t0));
        return t0;
}

static Type *
LookEnv(Ty *ty, TypeEnv *env, u32 id)
{
        if (env == NULL) {
                return NULL;
        } else {
                Value const *v = itable_lookup(ty, &env->vars, id);
                return (v == NULL || v->type == VALUE_NIL) ? NULL : v->ptr;
        }
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

inline static bool
already_visiting(TypeVector const *types, Type const *t0)
{
        for (int i = 0; i < vN(*types); ++i) {
                if (t0 == v__(*types, i)) {
                        return true;
                }
        }

        return false;
}

typedef struct {
        Type const *t0;
        Type const *t1;
} TypePair;

typedef vec(TypePair) TypePairVector;

inline static void
visit_pair(TypePairVector *pairs, Type const *t0, Type const *t1)
{
        xvP(*pairs, ((TypePair){ t0, t1 }));
}

inline static bool
already_visiting_pair(TypePairVector const *pairs, Type const *t0, Type const *t1)
{
        for (int i = 0; i < vN(*pairs); ++i) {
                TypePair const *pair = v_(*pairs, i);
                dont_printf("already_visiting?(%d/%zu)\n", i, vN(*pairs));
                dont_printf("  t0 = %s\n", ShowType(t0));
                dont_printf("  t1 = %s\n", ShowType(t1));

                dont_printf("  p0 = %s\n", ShowType(pair->t0));
                dont_printf("  p1 = %s\n\n\n", ShowType(pair->t1));
                if (SameType(pair->t0, t0) && SameType(pair->t1, t1)) {
                        return true;
                }
        }

        return false;
}

static void
AddConstraint(Ty *ty, Type *t0, Type *t1)
{
        Expr const *fun = TyCompilerState(ty)->func;

        if (fun == NULL) {
                TypeError("lowkey type shit");
        }

        ConstraintVector *cons = &fun->_type->constraints;

        avP(
                *cons,
                ((Constraint){
                        .type = TC_EQ,
                        .t0 = t0,
                        .t1 = t1
                })
        );
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
IsError(Type const *t0)
{
        return TypeType(t0) == TYPE_ERROR;
}

inline static bool
IsComputed(Type const *t0)
{
        return TypeType(t0) == TYPE_COMPUTED;
}

inline static bool
IsBottom(Type const *t0)
{
        return t0 == NULL || t0->type == TYPE_BOTTOM;
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
CanBind(Type const *t0)
{
        return IsUnboundVar(t0) && !IsTVar(t0);
}

inline static bool
IsUnboundVariadic(Type const *t0)
{
        return IsUnboundVar(t0) && t0->variadic;
}

inline static bool
CanBindVariadic(Type const *t0)
{
        return IsUnboundVariadic(t0) && !IsTVar(t0);
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

static bool
CanResolveAlias(Type const *t0)
{
        return (TypeType(t0) == TYPE_ALIAS)
            && (vN(t0->args) == vN(t0->bound))
            && (t0->_type != NULL);
}

static bool
CanCompute(Type const *t0)
{
        if (!IsComputed(t0) || !t0->inst || t0->val != NULL) {
                return false;
        }

        for (int i = 0; i < vN(t0->args); ++i) {
                if (!IsSolved(v__(t0->args, i))) {
                        return false;
                }
        }

        return true;
}

static bool
CanStep(Type const *t0)
{
        switch (TypeType(t0)) {
        case TYPE_VARIABLE:
                return IsBoundVar(t0);

        case TYPE_SLICE:
        case TYPE_SUBSCRIPT:
                return !IsUnboundVar(ResolveVar(t0->val));
        }

        return false;
}

inline static Type *
StepVar(Type const *t0)
{
        switch (TypeType(t0)) {
        case TYPE_VARIABLE:
                return IsBoundVar(t0) ? t0->val : (Type *)t0;

        case TYPE_SUBSCRIPT:
                return NthType(ResolveVar(t0->val), t0->i);

        case TYPE_SLICE:
                return SliceType(ty, ResolveVar(t0->val), t0->i, t0->j, t0->k);

        case TYPE_COMPUTED:
        {
        }

        default:
                return (Type *)t0;
        }
}

inline static void
BindVar(Type *var, Type *val)
{
        XXTLOG("Bind(): %s := %s", ShowType(var), ShowType(val));
        if (var->val != TVAR) {
                var->val = val;
                var->level = -1;
                var->bounded = true;
                if (val != NULL) {
                        if (var->src == NULL) var->src = val->src;
                        if (val->src == NULL) val->src = var->src;
                }
        }
}

inline static void
BindVarSoft(Type *var, Type *val)
{
        XXTLOG("BindSoft(): %s := %s", ShowType(var), ShowType(val));
        if (var->val != TVAR) {
                var->val = val;
                var->level = -1;
        } else {
                TLOG("*** NOT BINDING ***");
        }
}

static Type *
SeqToList(Type *t0)
{
        switch (TypeType(t0)) {
        case TYPE_SEQUENCE:
                t0->type = TYPE_LIST;
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        SeqToList(v__(t0->types, i));
                }
                break;

        case TYPE_VARIABLE:
                SeqToList(t0->val);
                break;
        }

        return t0;
}

inline static Type *
Unlist(Ty *ty, Type const *t0)
{
        return ListItem(ty, t0, 0, NIL_TYPE);
}

inline static bool
IsAny(Type const *t0)
{
        return t0 != NULL
            && t0->type == TYPE_OBJECT
            && t0->class->i == CLASS_TOP;
}

inline static bool
IsFixed(Type const *t0)
{
        return t0 != NULL && t0->fixed;
}

inline static bool
IsForgiving(Type const *t0)
{
        return t0 != NULL && t0->forgive;
}

inline static bool
IsUnknown(Type const *t0)
{
        return IsBottom(t0) && IsFixed(t0);
}

inline static bool
IsNil(Type const *t0)
{
        return t0 != NULL
            && t0->type == TYPE_NIL;
}

inline static bool
IsVariadic(Type const *t0)
{
        return (t0 != NULL) && t0->variadic;
}

inline static bool
IsVariadicFun(Type const *t0)
{
        if (t0 == NULL || t0->type != TYPE_FUNCTION) {
                return false;
        }

        for (int i = 0; i < vN(t0->params); ++i) {
                if (v_(t0->params, i)->rest) {
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

        for (int i = 0; i < vN(t0->params); ++i) {
                if (v_(t0->params, i)->kws) {
                        return true;
                }
        }

        return false;
}

static Type *
NewType(Ty *ty, int type)
{
        Type *t0 = amA0(sizeof *t0);
        t0->type = type;
        return t0;
}

static Type *
(NewRecord)(Ty *ty, ...)
{
        Type *t0 = NewType(ty, TYPE_TUPLE);

        Type *t1;
        char const *name;

        va_list ap;
        va_start(ap, ty);

        while ((name = va_arg(ap, char const *)) != NULL) {
                t1 = va_arg(ap, Type *);
                avP(t0->names, name);
                avP(t0->types, t1);
        }

        va_end(ap);

        return t0;
}

static Type *
(NewFunction)(Ty *ty, ...)
{
        Type *t0 = NewType(ty, TYPE_FUNCTION);
        Type *t1 = NULL;
        Type *t2;

        char const *name = NULL;
        bool optional = false;

        va_list ap;
        va_start(ap, ty);

        while ((t2 = va_arg(ap, Type *)) != NULL) {
                if (t2 == OPTIONAL) {
                        optional = true;
                } else if (t2 == NAMED) {
                        name = va_arg(ap, char const *);
                } else if (t1== NULL) {
                        t1 = t2;
                } else {
                        avP(t0->params, PARAM(name, t1, !optional));
                        name = NULL;
                        optional = false;
                        t1 = t2;
                }
        }

        va_end(ap);

        t0->rt = t1;

        return t0;
}

static Type *
(NewObject)(Ty *ty, int class, ...)
{
        Type *t0 = NewType(ty, TYPE_OBJECT);
        Type *t1;

        va_list ap;
        va_start(ap, class);

        t0->class = class_get_class(ty, class);

        while ((t1 = va_arg(ap, Type *)) != NULL) {
                avP(t0->args, t1);
        }

        va_end(ap);

        return t0;
}

static Type *
NewVar(Ty *ty)
{
        Type *t0;

        if (CheckConstraints) {
                t0 = NewType(ty, TYPE_VARIABLE);
                t0->id = NextID++;
                t0->level = CurrentLevel;
        } else {
                t0 = UNKNOWN;
        }

        return t0;
}

static Type *
NewForgivingVar(Ty *ty)
{
        Type *t0 = NewVar(ty);
        t0->forgive = true;
        return t0;
}

static Type *
NewTVar(Ty *ty)
{
        Type *t0 = NewVar(ty);
        t0->val = TVAR;
        t0->concrete = true;
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
        Type *p0 = NewTVar(ty);
        avP(t0->bound, p0->id);
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
                t->src = t0->src;
        }

        return t;
}

inline static imax
iwrap(imax i, imax n)
{
        return (i < 0) ? (i + n) : i;
}

static Type *
SliceTypes(Ty *ty, TypeVector const *types, imax i, imax j, imax k)
{
        Type *t0 = NewType(ty, TYPE_SEQUENCE);
        int n = vN(*types);

        if (k < 0) {
                int hi = min(iwrap(i - 1, n), n);
                int lo = max(iwrap(j, n), 0);
                for (int ix = hi; ix >= lo; ix += k) {
                        if (ix >= 0 && ix < n) {
                                avP(t0->types, v__(*types, ix));
                        }
                }
        } else {
                int lo = max(iwrap(i, n), 0);
                int hi = min(iwrap(j, n), n);
                for (int ix = lo; ix < hi; ix += k) {
                        if (ix >= 0 && ix < n) {
                                avP(t0->types, v__(*types, ix));
                        }
                }
        }

        return t0;
}

inline static Type *
TailTypes(Ty *ty, TypeVector const *types, int i)
{
        return SliceTypes(ty, types, i, INT_MAX, 1);
}

static Type *
SliceType(Ty *ty, Type const *t0, int i, int j, int k)
{
        Type *t1 = BOTTOM;

        XXTLOG("SliceType(%d, %d, %d):", i, j, k);
        XXTLOG("    %s", ShowType(t0));

        switch (TypeType(t0)) {
        case TYPE_SEQUENCE:
        case TYPE_LIST:
        case TYPE_TUPLE:
        case TYPE_UNION:
        case TYPE_INTERSECT:
                t1 = SliceTypes(ty, &t0->types, i, j, k);
                break;

        case TYPE_OBJECT:
        case TYPE_ALIAS:
                t1 = SliceTypes(ty, &t0->args, i, j, k);
                break;
        }

        XXTLOG("    %s\n", ShowType(t1));

        return t1;
}

static bool
FlattenTypeSequence(Ty *ty, TypeVector *types, ConstStringVector *names)
{
        bool already_flat = true;

        for (int i = 0; i < vN(*types); ++i) {
                Type *t0 = ResolveVar(v__(*types, i));
                if (TypeType(t0) == TYPE_SEQUENCE) {
                        already_flat = false;
                        break;
                }
        }

        if (already_flat) {
                return false;
        }

        TypeVector flat = {0};
        ConstStringVector flat_names = {0};

        for (int i = 0; i < vN(*types); ++i) {
                Type *t0 = ResolveVar(v__(*types, i));
                if (TypeType(t0) == TYPE_SEQUENCE) {
                        avPv(flat, t0->types);
                        if (names != NULL) {
                                while (vN(flat_names) < vN(flat)) {
                                        avP(flat_names, NULL);
                                }
                        }
                } else {
                        avP(flat, v__(*types, i));
                        if (names != NULL) {
                                avP(flat_names, v__(*names, i));
                        }
                }
        }

        FlattenTypeSequence(ty, &flat, (names != NULL) ? &flat_names : NULL);

        Type before = { .type = TYPE_SEQUENCE, .types = *types };
        Type after = { .type = TYPE_SEQUENCE, .types = flat };

        XXTLOG("flat():");
        XXTLOG("    %s", ShowType(&before));
        XXTLOG("    %s", ShowType(&after));

        *types = flat;
        if (names != NULL) {
                *names = flat_names;
        }

        return true;
}

inline static bool
Flatten(Ty *ty, Type *t0)
{
        switch (TypeType(t0)) {
        case TYPE_TUPLE:
                return FlattenTypeSequence(ty, &t0->types, &t0->names);
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                return FlattenTypeSequence(ty, &t0->types, NULL);
        case TYPE_ALIAS:
        case TYPE_OBJECT:
                return FlattenTypeSequence(ty, &t0->args, NULL);
        default:
                return false;
        }
}

static Type *
Reduce(Ty *ty, Type const *t0)
{
        Type *t1 = ResolveVar(t0);
        Type *t2;
        Type *t3;
        bool cloned = false;

        switch (TypeType(t1)) {
        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
        case TYPE_LIST:
        case TYPE_SEQUENCE:
                for (int i = 0; i < vN(t1->types); ++i) {
                        t2 = v__(t1->types, i);
                        t3 = Reduce(ty, t2);
                        if (t3 != t2 && !cloned) {
                                t1 = CloneType(ty, t1);
                                CloneVec(t1->types);
                                cloned = true;
                        }
                        *v_(t1->types, i) = t3;
                }
                t1 = Uniq(ty, t1);
                break;

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                t2 = Reduce(ty, t1->val);
                if (t2 != t1->val) {
                        t1 = CloneType(ty, t1);
                }
                t1->val = t2;
                break;

        case TYPE_OBJECT:
        case TYPE_ALIAS:
                for (int i = 0; i < vN(t1->args); ++i) {
                        t2 = v__(t1->args, i);
                        t3 = Reduce(ty, t2);
                        if (t3 != t2 && !cloned) {
                                t1 = CloneType(ty, t1);
                                CloneVec(t1->args);
                                cloned = true;
                        }
                        *v_(t1->args, i) = t3;
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t1->params); ++i) {
                        Param const *p = v_(t1->params, i);
                        t2 = Reduce(ty, p->type);
                        if (t2 != p->type && !cloned) {
                                t1 = CloneType(ty, t1);
                                CloneVec(t1->params);
                                cloned = true;
                        }
                        *v_(t1->params, i) = *p;
                        v_(t1->params, i)->type = t2;
                }
                t2 = Reduce(ty, t1->rt);
                if (t2 != t1->rt && !cloned) {
                        t1 = CloneType(ty, t1);
                }
                t1->rt = t2;
                break;
        }

        if (t1 != ResolveVar(t0)) {
                XXTLOG("reduce():");
                XXTLOG("    %s", ShowType(t0));
                XXTLOG("    %s", ShowType(t1));
        }

        return t1;
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
ExprTypeOr(Expr const *e, Type const *t0)
{
        if (e == NULL || e->_type == NULL) {
                return (Type *)t0;
        }

        return e->_type;
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
            && t0->class->i != CLASS_TOP
            && t0->class->type->type == TYPE_TAG;
}

inline static int
TagOf(Type const *t0)
{
        return (IsTagged(t0) || t0->type == TYPE_TAG)
             ? t0->class->type->tag
             : -1;
}

inline static bool
IsObject(Type const *t0)
{
        return (TypeType(t0) == TYPE_OBJECT)
            && !IsTagged(t0);
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
                return vN(t0->bound);
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
TypeArg(Type const *t0, int i)
{
        while (IsBoundVar(t0)) {
                t0 = t0->val;
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
                return ANY;
        }

        return v__(t0->args, i);
}

inline static Type *
NthType(Type const *t0, int i)
{
        t0 = ResolveVar(t0);

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                if (vN(t0->args) > i) {
                        return v__(t0->args, i);
                }
                break;

        case TYPE_SEQUENCE:
        case TYPE_LIST:
        case TYPE_TUPLE:
                if (vN(t0->types) > i) {
                        return v__(t0->types, i);
                }
                break;
        }

        return BOTTOM;
}

static bool
IsRecordLike(Type const *t0)
{
        t0 = ResolveVar(t0);

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                return !IsTagged(t0);

        case TYPE_CLASS:
        case TYPE_TUPLE:
                return true;

        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!IsRecordLike(v__(t0->types, i))) {
                                return false;
                        }
                }
                return true;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (IsRecordLike(v__(t0->types, i))) {
                                return true;
                        }
                }
                return false;
        }

        return false;
}

inline static Type *
ResolveVar(Type const *t0)
{
        while (CanStep(t0)) {
                t0 = StepVar(t0);
        }

        return (Type *)t0;
}


static Type *
ComputeType(Ty *ty, Type const *t0)
{
        Value val;

        for (int i = 0; i < vN(t0->args); ++i) {
                val = type_to_ty(ty, v__(t0->args, i));
                vmP(&val);
        }

        val = vmC(&t0->func, vN(t0->args));

        ((Type *)t0)->val = type_from_ty(ty, &val);

        XXTLOG("compute():");
        XXTLOG("    t0: %s", ShowType(t0));
        XXTLOG("    t1: %s", ShowType(t0->val));

        return t0->val;
}

inline static Type *
Resolve(Ty *ty, Type const *t0)
{
        Type const *t = t0;

        for (;;) {
                if (CanStep(t0)) {
                        t0 = StepVar(t0);
                } else if (CanResolveAlias(t0)) {
                        t0 = ResolveAlias(ty, t0);
                } else if (CanCompute(t0)) {
                        t0 = ComputeType(ty, t0);
                } else {
                        break;
                }
        }

        TLOG("Resolve(%d):", TypeType(t));
        TLOG("    %s", ShowType(t));
        TLOG("    %s\n", ShowType(t0));

        return (Type *)t0;
}

static bool
SameType(Type const *t0, Type const *t1)
{
        TLOG("SameType():");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s\n", ShowType(t1));

        if (t0 == t1) {
                return true;
        }

        if (IsBoundVar(t0)) {
                return false;
        }

        if (IsBoundVar(t1)) {
                return false;
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

        case PAIR_OF(TYPE_LIST):
        case PAIR_OF(TYPE_SEQUENCE):
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
                        char const *n0 = v__(t0->names, i);
                        char const *n1 = v__(t1->names, i);
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
                if (vN(t0->bound) != vN(t1->bound)) {
                        return false;
                }
                if (vN(t0->params) != vN(t1->params)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param const *p0 = v_(t0->params, i);
                        Param const *p1 = v_(t1->params, i);
                        if (p0->name != p1->name) {
                                if (p0->name == NULL || p1->name == NULL) {
                                        return false;
                                }
                                if (strcmp(p0->name, p1->name) != 0) {
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

        case PAIR_OF(TYPE_ALIAS):
                if (vN(t0->bound) != vN(t1->bound) || vN(t0->args) != vN(t1->args)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->bound); ++i) {
                        if (v__(t0->bound, i) != v__(t1->bound, i)) {
                                return false;
                        }
                }
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (!SameType(v__(t0->args, i), v__(t1->args, i))) {
                                return false;
                        }
                }
                return SameType(t0->_type, t1->_type);
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

        TLOG("Untagged(%s):", tags_name(ty, tag));
        TLOG("    %s", ShowType(t0));
        TLOG("    %s\n", ShowType(t1));

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
                        unify2(ty, &t2, t1);
                }
                return t2;

        case TYPE_OBJECT:
                t2 = type_member_access_t(ty, t0, name, false);
                return t2;
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
IsConcrete_(Type *t0)
{
        if (IsBottom(t0)) {
                return true;
        }

        if (t0->concrete) {
                return true;
        }

        switch (t0->type) {
        case TYPE_VARIABLE:
                return IsTVar(t0)
                    || (IsBoundVar(t0) && IsFixed(t0) && IsConcrete_(t0->val));

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
                if (!t0->fixed) {
                        return false;
                }
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!IsConcrete_(v__(t0->types, i))) {
                                return false;
                        }
                }
                return true;

        case TYPE_CLASS:
        case TYPE_OBJECT:
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (!IsConcrete_(v__(t0->args, i))) {
                                return false;
                        }
                }
                return true;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (!IsConcrete_(v__(t0->args, i))) {
                                return false;
                        }
                }
                if (!IsConcrete_(t0->rt)) {
                        return false;
                }
                return true;


        case TYPE_INTEGER:
        case TYPE_NIL:
                return true;
        }

        return true;
}

static bool
IsConcrete(Type *t0)
{
        return (t0 != NULL) && t0->concrete;

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

        if (IsNil(t0)) {
                return CLASS_NIL;
        }

        if (TypeType(t0) != TYPE_OBJECT) {
                return CLASS_BOTTOM;
        }

        return t0->class->i;
}

static int
ClassOfType(Ty *ty, Type const *t0)
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

        case TYPE_NIL:
                return CLASS_NIL;
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
                        unify2(ty, &t, v__(t0->types, i));
                }
                break;

        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify2(ty, &t, UnionOf(ty, v__(t0->types, i)));
                }
                break;

        case TYPE_OBJECT:
                c = class_get_class(ty, ClassOfType(ty, t0));
                for (int i = 0; i < vN(c->fields.values); ++i) {
                        Value const *field = v_(c->fields.values, i);
                        unify2(
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

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                ret = RefersTo(t0->val, id);
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
        case TYPE_SEQUENCE:
        case TYPE_LIST:
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
                for (int i = 0; i < vN(t0->params); ++i) {
                        if (RefersTo(v_(t0->params, i)->type, id)) {
                                ret = true;
                                break;
                        }
                }
                break;

        case TYPE_OBJECT:
        case TYPE_COMPUTED:
        case TYPE_CLASS:
        case TYPE_ALIAS:
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
        switch (TypeType(t0)) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (type_check(ty, v__(t0->types, i), t1)) {
                                return true;
                        }
                }
                break;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (type_check(ty, t1, v__(t0->types, i))) {
                                return true;
                        }
                }
                break;
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

        if (!CheckConstraints) {
                return t0;
        }

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
                if (vN(t0->types) == 1) {
                        t1 = v__(t0->types, 0);
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

        return t1;
}

static Type *
Either(Ty *ty, Type const *t0, Type const *t1)
{
        t0 = type_unfixed(ty, ResolveVar(t0));
        t1 = type_unfixed(ty, ResolveVar(t1));

        if (t0 == NULL) {
                return (Type *)t1;
        }

        if (t1 == NULL) {
                return (Type *)t0;
        }

        if (CheckConstraints) {
                if (type_check(ty, (Type *)t0, (Type *)t1)) {
                        return (Type *)t0;
                }

                if (type_check(ty, (Type *)t1, (Type *)t0)) {
                        return (Type *)t1;
                }
        }

        Type *t2 = NewType(ty, TYPE_UNION);

        t2->src = (t0->src != NULL) ? t0->src : t1->src;

        if (IsFixed(t0)) {
                avP(t2->types, t0);
        } else for (int i = 0; i < UnionCount(t0); ++i) {
                avP(t2->types, UnionElem(t0, i));
        }
        if (IsFixed(t1)) {
                avP(t2->types, t1);
        } else for (int i = 0; i < UnionCount(t1); ++i) {
                avP(t2->types, UnionElem(t1, i));
        }

        return Uniq(ty, t2);
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
        t->concrete = true;

        if (class->def != NULL) {
                for (int i = 0; i < vN(class->def->class.type_params); ++i) {
                        Type *t0 = type_resolve(
                                ty,
                                v__(class->def->class.type_params, i)
                        );
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
        t->concrete = true;

        byte_vector name = {0};
        dump(&name, "%s", var->identifier);
        *itable_get(ty, &VarNameTable, t->id) = PTR(name.items);

        xvP(FixedTypeVars, t->id);

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
type_alias(Ty *ty, Symbol *var, Stmt const *def)
{
        static TypeVector refs;

        if (!ENABLED) {
                return UNKNOWN;
        }

        var->type = NewType(ty, TYPE_ALIAS);
        var->type->concrete = true;

        for (int i = 0; i < vN(def->class.type_params); ++i) {
                Type *t0 = type_resolve(
                        ty,
                        v__(def->class.type_params, i)
                );
                avP(
                        var->type->bound,
                        t0->id
                );
        }

        v0(refs);

        var->type->name = def->class.name;
        var->type->_type = MakeConcrete(ty, type_resolve(ty, def->class.type), &refs);

        for (int i = 0; i < vN(refs); ++i) {
                dont_printf("=== Patch #%d (%s) ===\n", i, var->type->name);
                v__(refs, i)->_type = var->type->_type;
        }

        XXTLOG("type_alias(%s): %s\n", def->class.name, ShowType(var->type->_type));

        return var->type;
}

Type *
type_tag(Ty *ty, Class *class, int tag)
{
        Type *t = NewType(ty, TYPE_TAG);
        t->class = class;
        t->tag = tag;
        t->concrete = true;

        Type *t0 = NewVar(ty);
        t0->val = TVAR;
        t0->concrete = true;
        avP(t->bound, t0->id);

        class->type = t;
        class->object_type = NewType(ty, TYPE_OBJECT);
        class->object_type->class = class;
        class->object_type->concrete = true;
        avP(class->object_type->args, t0);

        return t;
}

Type *
type_class(Ty *ty, Class *class)
{
        Type *t = NewType(ty, TYPE_CLASS);
        t->class = class;
        t->concrete = true;

        if (class->def != NULL) {
                for (int i = 0; i < vN(class->def->class.type_params); ++i) {
                        //Type *t0 = type_resolve(
                        //        ty,
                        //        v__(class->def->class.type_params, i)
                        //);
                        Symbol *var = v__(class->def->class.type_params, i)->symbol;
                        avP(t->bound, var->type->id);
                        t->variadic |= SymbolIsVariadic(var);
                }
        }

        return t;
}

Type *
type_function(Ty *ty, Expr const *e, bool tmp)
{
        Type *t = NewType(ty, TYPE_FUNCTION);

        //fprintf(stderr, "================== %s ======================\n", e->name);

        if (e->return_type != NULL) {
                Type *rt = SeqToList(type_resolve(ty, e->return_type));
                if (e->class > -1) {
                        Class *class = class_get_class(ty, e->class);
                        rt = SolveMemberAccess(ty, class->object_type, rt);
                }
                t->rt = MakeConcrete(ty, rt, NULL);
        } else {
                t->rt = tmp ? AddParam(ty, t) : NewHole(ty);
        }

        if (e->yield_type != NULL) {
                t->yields = type_fixed(ty, type_resolve(ty, e->yield_type));
        }

        for (int i = 0; i < vN(e->type_params); ++i) {
                Symbol *var = v__(e->type_params, i)->symbol;
                avP(t->bound, var->type->id);
                t->variadic |= SymbolIsVariadic(var);
        }

        for (int i = 0; i < vN(e->param_symbols); ++i) {
                Symbol *psym = v__(e->param_symbols, i);

                Type *p0 = psym->type;
                if (p0 == NULL) {
                        p0 = tmp ? AddParam(ty, t) : NewVar(ty);
                }

                if (!tmp) {
                        if (i == e->rest) {
                                psym->type = type_fixed(ty, ArrayOf(ty, p0));
                        } else if (i == e->ikwargs) {
                                psym->type = type_fixed(ty, DictOf(ty, TYPE_STRING, p0));
                        } else if (psym->type == NULL && v__(e->dflts, i) != NULL) {
                                psym->type = p0;
                                p0 = Either(ty, p0, NIL_TYPE);
                        } else {
                                psym->type = p0;
                        }
                }

                avP(
                        t->params,
                        PARAMx(
                                .name = psym->identifier,
                                .type = p0,
                                .rest = (i == e->rest),
                                .kws  = (i == e->ikwargs),
                                .required = (
                                        v__(e->dflts, i) == NULL
                                     && (i != e->rest)
                                     && (i != e->ikwargs)
                                     && (
                                                v__(e->constraints, i) == NULL
                                             || !type_check(
                                                        ty,
                                                        v__(e->constraints, i)->_type,
                                                        NIL_TYPE
                                                )
                                        )
                                )
                        )
                );
                //psym->type = type_fixed(ty, psym->type);
        }

        if (!tmp && e->function_symbol != NULL) {
                e->function_symbol->type = t;
        }

        return t;
}

inline static Type *
Relax(Type *t0)
{
        switch (TypeType(t0)) {
        case TYPE_INTEGER:
                return TYPE_INT;
        }

        return t0;
}

static void
GatherFree(Ty *ty, Type *t0, U32Vector *freev, U32Vector *boundv)
{
        static int d = 0;

        dont_printf("%*sGatherFree(%s)\n", 4*d, "", ShowType(t0));

        t0 = ResolveVar(t0);

        if (t0 == NULL || t0->concrete) {
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
                        GatherFree(ty, t0->val, freev, boundv);
                } else if (
                        (boundv == NULL || !ContainsID(boundv, t0->id))
                     && (t0->level > CurrentLevel)
                ) {
                        if (!ContainsID(freev, t0->id)) {
                                avP(*freev, t0->id);
                        }
                }
                break;

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                GatherFree(ty, t0->val, freev, boundv);
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
        case TYPE_LIST:
        case TYPE_SEQUENCE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        GatherFree(ty, v__(t0->types, i), freev, boundv);
                }
                break;

        case TYPE_ALIAS:
        case TYPE_OBJECT:
        case TYPE_COMPUTED:
                for (int i = 0; i < vN(t0->args); ++i) {
                        GatherFree(ty, v__(t0->args, i), freev, boundv);
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_FUNCTION:
                if (boundv != NULL) {
                        avPv(*boundv, t0->bound);
                }
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
                        GatherFree(ty, p->type, freev, boundv);
                }
                GatherFree(ty, t0->rt, freev, boundv);
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

        Type *t = t0;

        if (drill) {
                t0 = Resolve(ty, t0);
        }

        switch (mode) {
        case PROP_FIX:   t0 = type_fixed(ty, t0);   break;
        case PROP_UNFIX: t0 = type_unfixed(ty, t0); break;
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
                                t0->concrete &= IsConcrete(t1);
                        }
                        t0->val = t1;
                } else {
                        t1 = LookEnv(ty, ty->tenv, t0->id);
                        t0 = (t1 != NULL) ? t1 : t0;
                }
                break;

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                t1 = PropagateX(ty, t0->val, drill, mode);
                if (t1 != t0->val) {
                        t0 = CloneType(ty, t0);
                        t0->concrete &= IsConcrete(t1);
                }
                t0->val = t1;
                break;

        case TYPE_LIST:
        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
        case TYPE_SEQUENCE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        t2 = PropagateX(ty, t1, drill, mode);
                        if (t2 != t1 && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->types);
                                cloned = true;
                        }
                        *v_(t0->types, i) = t2;
                        t0->concrete &= IsConcrete(t2);
                }
                Flatten(ty, t0);
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
                        t0->concrete &= IsConcrete(t2);
                }
                break;

        case TYPE_COMPUTED:
                for (int i = 0; i < vN(t0->args); ++i) {
                        t1 = v__(t0->args, i);
                        t2 = PropagateX(ty, t1, drill, mode);
                        if (t2 != t1 && !cloned) {
                                t0 = CloneType(ty, t0);
                                t0->inst = true;
                                CloneVec(t0->args);
                                cloned = true;
                        }
                        *v_(t0->args, i) = t2;
                        t0->concrete &= IsConcrete(t2);
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
                        t0->concrete &= IsConcrete(t2);
                }
                t1 = type_fixed(ty, Inst(ty, t0->_type, &t0->bound, &t0->args));
                if (t1 != t0->_type && !cloned) {
                        t0 = CloneType(ty, t0);
                        t0->concrete &= IsConcrete(t1);
                }
                t0->_type = t1;
                break;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
                        t1 = PropagateX(ty, p->type, drill, mode);
                        if (t1 != p->type && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->params);
                                cloned = true;
                        }
                        *v_(t0->params, i) = *p;
                        v_(t0->params, i)->type = t1;
                        t0->concrete &= IsConcrete(t1);
                }
                t1 = PropagateX(ty, t0->rt, drill, mode);
                if (t1 != t0->rt && !cloned) {
                        t0 = CloneType(ty, t0);
                }
                t0->concrete &= IsConcrete(t1);
                t0->rt = t1;
                break;
        }

        d -= 1;
        vvX(visiting);

        TLOG("%*sPropagate()", 4*d, "");
        TLOG("%*s    %s", 4*d, "", ShowType(t));
        TLOG("%*s    %s", 4*d, "", ShowType(t0));

        return t0;
}

static Type *
Propagate(Ty *ty, Type *t0)
{
        Type *t1 = PropagateX(ty, t0, false, PROP_DEFAULT);
        return t1;
}

static bool
Occurs(Ty *ty, Type *t0, u32 id, int level)
{
        static int d = 0;

        dont_printf("%*sOccurs(%s)\n", 4*d, "", ShowType(t0));

        if (IsConcrete(t0)) {
                return false;
        }

        t0 = Resolve(ty, t0);

        if (IsConcrete(t0)) {
                return false;
        }

        if (IsBottom(t0)) {
                return IsFixed(t0) ? false : (level == -1);
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
                        ret = (level == -1 && !IsFixed(t0)) || Occurs(ty, t0->val, id, level);
                } else if (!IsTVar(t0)) {
                        if (level == -1) {
                                ret = true;
                        } else {
                                t0->level = min(t0->level, level);
                                ret = t0->id == id;
                        }
                }
                break;

        case TYPE_SLICE:
        case TYPE_SUBSCRIPT:
                ret = Occurs(ty, t0->val, id, level);
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (Occurs(ty, v__(t0->types, i), id, level)) {
                                ret = true;
                                break;
                        }
                }
                break;

        case TYPE_ALIAS:
        case TYPE_OBJECT:
        case TYPE_COMPUTED:
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

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
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
        U32Vector freev = {0};
        U32Vector boundv = {0};

        switch (TypeType(t0)) {
        case TYPE_FUNCTION:
                GatherFree(ty, t0, &freev, NULL);
                for (int i = 0; i < vN(t0->bound); ++i) {
                        if (RefersTo(t0, v__(t0->bound, i))) {
                                avP(freev, v__(t0->bound, i));
                        }
                }
                dont_printf("Free(%s): ", ShowType(t0));
                for (int i = 0; i < vN(freev); ++i) {
                        dont_printf("%s%s", (i > 0) ? ", " : "", VarName(ty, v__(freev, i)));
                }
                dont_printf("\n");
                if (true || vN(freev) != 0) {
                        t1 = CloneType(ty, t0);
                        v00(t1->bound);
                        for (int i = 0; i < vN(freev); ++i) {
                                if (!ContainsID(&t1->bound, v__(freev, i))) {
                                        avP(t1->bound, v__(freev, i));
                                }
                        }
                }
                break;
        }

        TLOG("Generalize()");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s", ShowType(t1));

        return t1;
}

static Type *
NewInst0(Ty *ty, Type *t0, TypeEnv *env)
{
        static TypeVector visiting;

        if (CanBind(t0)) {
                Type *t1 = LookEnv(ty, env, t0->id);
                if (t1 == NULL) {
                        t1 = PutEnv(ty, env, t0->id, NewVar(ty));
                }
                return t1;
        }

        if (already_visiting(&visiting, t0)) {
                return UNKNOWN;
        } else {
                xvP(visiting, t0);
        }

        Type *t00 = t0;

        t0 = CloneType(ty, t0);

        switch (TypeType(t0)) {
        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        t0->val = NewInst0(ty, t0->val, env);
                }
                break;

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                t0 = CanStep(t0)
                   ? NewInst0(ty, StepVar(t0), env)
                   : t0;
                break;

        case TYPE_UNION:
                CloneVec(t0->types);
                for (int i = 0; i < vN(t0->types); ++i) {
                        *v_(t0->types, i) = NewInst0(ty, v__(t0->types, i), env);
                        if (IsAny(v__(t0->types, i))) {
                                t0 = ANY;
                                break;
                        }
                }
                break;

        case TYPE_INTERSECT:
                CloneVec(t0->types);
                for (int i = 0; i < vN(t0->types); ++i) {
                        *v_(t0->types, i) = NewInst0(ty, v__(t0->types, i), env);
                        if (IsBottom(v__(t0->types, i))) {
                                t0 = UNKNOWN;
                                break;
                        }
                }
                break;

        case TYPE_TUPLE:
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                CloneVec(t0->types);
                for (int i = 0; i < vN(t0->types); ++i) {
                        *v_(t0->types, i) = NewInst0(ty, v__(t0->types, i), env);
                }
                break;

        case TYPE_ALIAS:
        case TYPE_OBJECT:
                CloneVec(t0->args);
                for (int i = 0; i < vN(t0->args); ++i) {
                        *v_(t0->args, i) = NewInst0(ty, v__(t0->args, i), env);
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_FUNCTION:
                CloneVec(t0->params);
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param *p = v_(t0->params, i);
                        p->type = NewInst0(ty, p->type, env);
                }
                t0->rt = NewInst0(ty, t0->rt, env);
                break;

        case TYPE_INTEGER:
                t0->type = TYPE_OBJECT;
                t0->class = TYPE_INT->class;
                v00(t0->args);
                v00(t0->bound);
                break;
        }

        vvX(visiting);

        XXTLOG("NewInst():");
        XXTLOG("    %s", ShowType(t00));
        XXTLOG("    %s", ShowType(t0));

        return t0;
}

static Type *
NewInst(Ty *ty, Type *t0)
{
        return NewInst0(ty, t0, NewEnv(ty, NULL));
}

inline static void
combine(Ty *ty, Type **t0, Type *t1, bool super)
{
        if (super) {
                unify2_(ty, t0, t1, false);
        } else {
                type_intersect(ty, t0, t1);
        }
}

inline static void
AddMemo(TypeMemo *memo, Type const *t0, Type const *t1, bool b)
{
        xvP(memo->id0, t0);
        xvP(memo->id1, t1);
        xvP(memo->memo, b);
}

inline static bool
CheckMemo(TypeMemo const *memo, Type const *t0, Type const *t1, bool *b)
{
        for (int i = 0; i < vN(memo->memo); ++i) {
                if (
                        v__(memo->id0, i) == t0
                     && v__(memo->id1, i) == t1
                ) {
                        *b = v__(memo->memo, i);
                        return true;
                }
        }

        return false;
}

static void
xtrace(Ty *ty, Type const *t0, byte_vector *out, int depth)
{
        Expr const *expr = t0->src;

        if (CanStep(t0)) {
                xtrace(ty, StepVar(t0), out, depth);
        }

        if (expr != NULL) {
                dump(
                        out,
                        FMT_MORE "%*s%s%-24.24s%s:%s%5d%s  |  %s\n",
                        depth * 4,
                        "",
                        TERM(95),
                        expr->file != NULL ? expr->file : "(unknown)",
                        TERM(0),
                        TERM(92),
                        expr->start.line + 1,
                        TERM(0),
                        show_expr(expr)
                );
        }

        switch (TypeType(t0)) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        dump(
                                out,
                                FMT_MORE "%*s  %s(%d)%s %s",
                                depth * 4,
                                "",
                                TERM(33),
                                i + 1,
                                TERM(0),
                                ShowType(v__(t0->types, i))
                        );
                        xtrace(ty, v__(t0->types, i), out, depth + 1);
                }
                break;

        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        char const *name = v__(t0->names, i);
                        if (name == NULL) {
                                dump(
                                        out,
                                        FMT_MORE "%*s  %s[%d]%s %s",
                                        depth * 4,
                                        "",
                                        TERM(33),
                                        i + 1,
                                        TERM(0),
                                        ShowType(v__(t0->types, i))
                                );
                        } else {
                                dump(
                                        out,
                                        FMT_MORE "%*s  %s%s:%s %s",
                                        depth * 4,
                                        "",
                                        TERM(33),
                                        name,
                                        TERM(0),
                                        ShowType(v__(t0->types, i))
                                );
                        }
                        xtrace(ty, v__(t0->types, i), out, depth + 1);
                }
                break;
        }
}

static char *
trace(Ty *ty, Type const *t0)
{
        byte_vector buf = {0};

        xtrace(ty, t0, &buf, 0);

        if (vN(buf) == 0) {
                dump(&buf, " %s<unknown>%s\n", TERM(33), TERM(0));
        }

        return v_(buf, 0);
}

static Type *
GetTrait(Ty *ty, Type *t0, int i)
{
        if (
                TypeType(t0) != TYPE_OBJECT
             || IsTagged(t0)
        ) {
                return NULL;
        }

        if (t0->class->def == NULL) {
                return NULL;
        }

        ClassDefinition *def = &t0->class->def->class;

        if (vN(def->traits) <= i) {
                return NULL;
        }

        Type *trait0 = type_resolve(ty, v__(def->traits, i));

        return SolveMemberAccess(ty, t0, trait0);
}

static Type *
GetSuper(Ty *ty, Type *t0)
{
        if (
                TypeType(t0) != TYPE_OBJECT
             || IsTagged(t0)
        ) {
                return NULL;
        }

        if (t0->class->def == NULL) {
                return NULL;
        }

        ClassDefinition *def = &t0->class->def->class;

        if (def->super == NULL) {
                return NULL;
        }

        Type *super0 = type_resolve(ty, def->super);

        return SolveMemberAccess(ty, t0, super0);
}

static bool
GetField(Ty *ty, Type *t0, int i, Type **u0, char const **name)
{
        Expr const *field;

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                if (t0->class->def == NULL) {
                        *u0 = UNKNOWN;
                        *name = "";
                        return true;
                }
                if (i < vN(t0->class->def->class.fields)) {
                        field = v__(t0->class->def->class.fields, i);
                        *u0 = SolveMemberAccess(ty, t0, field->_type);
                        *name = FieldIdentifier(field)->identifier;
                        return true;
                }
                i -= vN(t0->class->def->class.fields);
                if (i < vN(t0->class->def->class.methods)) {
                        field = v__(t0->class->def->class.methods, i);
                        *u0 = SolveMemberAccess(ty, t0, field->_type);
                        *name = field->name;
                        return true;
                }
                return false;

        case TYPE_CLASS:
                if (t0->class->def == NULL) {
                        return NULL;
                }
                if (i < vN(t0->class->def->class.statics)) {
                        field = v__(t0->class->def->class.statics, i);
                        *u0 = SolveMemberAccess(ty, t0, field->_type);
                        *name = field->name;
                        return true;
                }
                return false;

        case TYPE_TUPLE:
                if (i < vN(t0->types) && v__(t0->names, i) != NULL) {
                        *u0 = v__(t0->types, i);
                        *name = v__(t0->names, i);
                        return true;
                }
                return false;
        }

        return false;
}

static bool
TryUnifyObjects(Ty *ty, Type *t0, Type *t1, bool super)
{
        if (!IsRecordLike(t0) || !IsRecordLike(t1)) {
                return false;
        }

        if (
                TypeType(t0) == TYPE_OBJECT
             && TypeType(t1) == TYPE_OBJECT
             && t0->class == t1->class
        ) {
                for (int i = 0; i < ArgCount(t0) && i < ArgCount(t1); ++i) {
                        Type *arg0 = v__(t0->args, i);
                        Type *arg1 = v__(t1->args, i);
                        if (CanBindVariadic(arg0)) {
                                BindVar(arg0, TailTypes(ty, &t1->args, i));
                                Flatten(ty, t0);
                                break;
                        } else if (CanBindVariadic(arg1)) {
                                BindVar(arg1, TailTypes(ty, &t0->args, i));
                                Flatten(ty, t1);
                                break;
                        } else if (!UnifyX(ty, TypeArg(t0, i), TypeArg(t1, i), super, false)) {
                                return false;
                        }
                }

                return true;
        }

        if (
                TypeType(t0) == TYPE_OBJECT
             && TypeType(t1) == TYPE_OBJECT
             && !class_is_subclass(
                     ty,
                     super ? t1->class->i : t0->class->i,
                     super ? t0->class->i : t1->class->i
                )
        ) {
                return false;
        }

        if (
                TypeType(t0) == TYPE_TUPLE
             && TypeType(t1) == TYPE_TUPLE
             && false
        ) {
                Type *t2;

                if (super) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                if (CanBindVariadic(v__(t0->types, i))) {
                                        BindVar(v__(t0->types, i), TailTypes(ty, &t1->types, i));
                                        Flatten(ty, t0);
                                        break;
                                }
                                char const *name = v__(t0->names, i);
                                t2 = (name != NULL)
                                   ? RecordField(ty, t1, name)
                                   : RecordElem(t1, i);
                                if (t2 == NULL) {
                                        return false;
                                }
                                //!UnifyX(ty, v__(t0->types, i), t2, super, false)) {
                                        unify2(ty, v_(t0->types, i), t2);
                                //}
                        }
                } else {
                        for (int i = 0; i < vN(t1->types); ++i) {
                                if (CanBindVariadic(v__(t1->types, i))) {
                                        BindVar(v__(t1->types, i), TailTypes(ty, &t0->types, i));
                                        Flatten(ty, t1);
                                        break;
                                }
                                char const *name = v__(t1->names, i);
                                t2 = (name != NULL)
                                   ? RecordField(ty, t0, name)
                                   : RecordElem(t0, i);
                                if (t2 != NULL && !UnifyX(ty, t2, v__(t1->types, i), super, false)) {
                                        combine(ty, v_(t1->types, i), t2, !super);
                                }
                        }
                }

                return true;
        }

        if (super) {
                for (int i = 0;; ++i) {
                        Type *trait1 = GetTrait(ty, t1, i);

                        if (trait1 == NULL) {
                                break;
                        }

                        if (UnifyX(ty, t0, trait1, super, false)) {
                                return true;
                        }
                }

                for (int i = 0;; ++i) {
                        Type *u0;
                        char const *name;

                        if (!GetField(ty, t0, i, &u0, &name)) {
                                break;
                        }

                        Type *u1 = type_member_access_t(ty, t1, name, false);

                        if (IsBottom(u1) && !IsUnknown(u1)) {
                                if (IsForgiving(u0)) {
                                        u1 = IsObject(t1) ? NewVar(ty) : NIL_TYPE;
                                } else if (
                                        TypeType(t1) == TYPE_TUPLE
                                     && !IsFixed(t1)
                                     && UnifyX(ty, t1, t0, true, false)
                                ) {
                                        *t1 = *t0;
                                        return true;
                                } else {
                                        return false;
                                }
                        }

                        if (!UnifyX(ty, Inst1(ty, u0), Inst1(ty, u1), super, false)) {
                                return false;
                        }
                }

                for (int i = 0;; ++i) {
                        Type *trait0 = GetTrait(ty, t0, i);

                        if (trait0 == NULL) {
                                break;
                        }

                        if (!UnifyX(ty, trait0, t1, super, false)) {
                                return false;
                        }
                }

                Type *super0 = GetSuper(ty, t0);

                return (super0 == NULL)
                    || UnifyX(ty, super0, t1, super, false);
        } else {
                for (int i = 0;; ++i) {
                        Type *trait0 = GetTrait(ty, t0, i);

                        if (trait0 == NULL) {
                                break;;
                        }

                        if (UnifyX(ty, trait0, t1, super, false)) {
                                return true;
                        }
                }

                for (int i = 0;; ++i) {
                        Type *u1;
                        char const *name;

                        if (!GetField(ty, t1, i, &u1, &name)) {
                                break;
                        }

                        Type *u0 = type_member_access_t(ty, t0, name, false);

                        if (IsBottom(u0) && !IsUnknown(u0)) {
                                if (IsForgiving(u1)) {
                                        u0 = NIL_TYPE;
                                } else {
                                        return false;
                                }
                        }

                        if (!UnifyX(ty, Inst1(ty, u0), Inst1(ty, u1), super, false)) {
                                return false;
                        }
                }

                for (int i = 0;; ++i) {
                        Type *trait1 = GetTrait(ty, t1, i);

                        if (trait1 == NULL) {
                                break;
                        }

                        if (!UnifyX(ty, t0, trait1, super, false)) {
                                return false;
                        }
                }

                Type *super1 = GetSuper(ty, t1);

                return (super1 == NULL)
                    || UnifyX(ty, t0, super1, super, false);
        }
}


static bool
UnifyXD(Ty *ty, Type *t0, Type *t1, bool super, bool check, bool soft)
{
#define UnifyXD(ty, t0, t1, su, ch, so) ((UnifyXD)(ty, t0, t1, su, ch, so) || ((DPRINT(check, "[%d]: %s   !%s   %s", __LINE__, ShowType(t0), (super ? ">" : "<"), ShowType(t1)), false)))
        static int d = 0;
        static TypePairVector visiting;

        TypeCheckCounter += 1;

        if (!FuelCheck()) {
                return false;
        }

        Type *_t0 = t0;
        Type *_t1 = t1;

        d += 1;

        char line[1024] = {0};
        for (int i = 0; i < d; ++i) {
                strcat(line, i + 1 == d ? "====" : "    ");
        }

        char const *color;
        switch (d) {
        case 0: color = TERM(33); break;
        case 1: color = TERM(34); break;
        case 2: color = TERM(95); break;
        case 3: color = TERM(96); break;
        case 4: color = TERM(35); break;
        case 5: color = TERM(36); break;
        default: color = TERM(98); break;
        }

        XXTLOG(
                "%s%s%sUnify%s(%s, %s):",
                color,
                line,
                check ? "" : "Try",
                TERM(0),
                super ? "super" : "sub",
                soft ? "soft" : "hard"
        );
        DPRINT(true, "    %s", ShowType(t0));
        DPRINT(true, "    %s", ShowType(t1));

        if (already_visiting_pair(&visiting, t0, t1)) {
                visit_pair(&visiting, t0, t1);
                goto Fail;
        } else {
                visit_pair(&visiting, t0, t1);
        }

        if (d > 72) {
                goto Fail;
        }

        if (IsConcrete(t0) && IsConcrete(t1)) {
                if (type_check(ty, super ? t0 : t1, super ? t1 : t0)) {
                        goto Success;
                } else {
                        goto Fail;
                }
        }

        for (;;) {
                if (CanResolveAlias(t0)) {
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

        DPRINT(true, "t0: %s", ShowType(t0));

        t1 = ResolveVar(t1);

        if (IsUnboundVar(t0) && !IsTVar(t0) && (!soft || IsHole(t0) || IsUnknown(t1))) {
                if (Occurs(ty, t1, t0->id, t0->level)) {
                        //BindVar(t0, BOTTOM);
                        goto Success;
                        //TypeError(
                        //        "can't unify:\n  %s\n  %s\n",
                        //        ShowType(t0),
                        //        ShowType(t1)
                        //);
                } else {
                        t0->bounded |= !super;
#if 0
                        if (super) {
                                BindVar(t0, Either(ty, t1, NewVar(ty)));
                        } else {
                                Type *t2 = NewType(ty, TYPE_INTERSECT);
                                avP(t2->types, t1);
                                avP(t2->types, NewVar(ty));
                                BindVar(t0, t2);
                        }
#else
                        BindVar(t0, type_unfixed(ty, Relax(Reduce(ty, t1))));
#endif
                        goto Success;
                }
        } else if (!soft && IsUnboundVar(t1) && !IsTVar(t1)) {
                if (Occurs(ty, t0, t1->id, t1->level)) {
                        //BindVar(t1, BOTTOM);
                        goto Success;
                } else {
                        t1->bounded |= super;
                        BindVar(t1, type_unfixed(ty, Relax(Reduce(ty, t0))));
                }
                goto Success;
        }

        if (type_check_shallow(ty, super ? t0 : t1, super ? t1 : t0)) {
                goto Success;
        }

        if (IsBoundVar(t0)) {
                if (UnifyXD(ty, t0->val, t1, super, false, soft)) {
                        goto Success;
                }
                if (super) {
                        if (!type_check(ty, t0->val, t1) || IsUnknown(t1)) {
                                unify2(ty, &t0->val, Relax(t1));
                        }
                } else {
                        t0->bounded = true;
                        if (!type_check(ty, t1, t0->val) || IsUnknown(t1)) {
                                type_intersect(ty, &t0->val, Relax(t1));
                        }
                }
        }

        t0 = Resolve(ty, t0);
        t1 = Resolve(ty, t1);

        if (IsComputed(t0) || IsComputed(t1)) {
                AddConstraint(ty, super ? t0 : t1, super ? t0 : t1);
        }

        Type *t0_ = IsConcrete(t0) ? Unlist(ty, t0) : t0;
        Type *t1_ = IsConcrete(t1) ? Unlist(ty, t1) : t1;

        if (!SameType(t0_, t0) || !SameType(t1_, t1)) {
                if (UnifyXD(ty, t0_, t1_, super, check, soft)) {
                        goto Success;
                } else {
                        goto Fail;
                }
        }

        if (
                IsUnboundVar(t0)
             && IsUnboundVar(t1)
             && t0->id == t1->id
        ) {
                goto Success;
        }

        if (IsBottom(t0) || (IsBottom(t1) && !IsFixed(t1))) {
                goto Success;
        }

        if (IsComputed(t0) || IsComputed(t1)) {
                goto Success;
        }

        if (type_check_x(ty, super ? t0 : t1, super ? t1 : t0, false)) {
                goto Success;
        }

        if (
                IsTagged(t0)
             && IsTagged(t1)
             && TagOf(t0) == TagOf(t1)
        ) {
                TLOG("Merge(%s):  %s   <--->   %s", soft ? "soft" : "hard", ShowType(t0), ShowType(t1));
                if (soft) {
                        UnifyXD(ty, v__(t0->args, 0), v__(t1->args, 0), super, check, soft);
                } else {
                        combine(ty, v_(t0->args, 0), v__(t1->args, 0), super);
                }
                if (UnifyX(ty, v__(t0->args, 0), v__(t1->args, 0), super, check)) {
                        goto Success;
                } else {
                        goto Fail;
                }
                TLOG("After: %s", ShowType(t0));
        }

        if (TypeType(t1) == TYPE_INTERSECT) {
                if (super) {
                        for (int i = 0; i < vN(t1->types); ++i) {
                                TypeEnv *env = NewEnv(ty, NULL);
                                if (
                                        UnifyXD(
                                                ty,
                                                NewInst0(ty, t0, env),
                                                NewInst0(ty, v__(t1->types, i),  env),
                                                super,
                                                false,
                                                soft
                                        )
                                ) {
                                        UnifyXD(
                                                ty,
                                                t0,
                                                v__(t1->types, i),
                                                super,
                                                false,
                                                soft
                                        );
                                        goto Success;
                                }
                        }
                        goto Fail;
                } else {
                        for (int i = 0; i < vN(t1->types); ++i) {
                                if (!UnifyXD(ty, t0, v__(t1->types, i), super, false, soft)) {
                                        goto Fail;
                                }
                        }
                        goto Success;
                }
        }

        if (TypeType(t0) == TYPE_UNION) {
                if (super) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                Type **t00 = v_(t0->types, i);
                                if (UnifyXD(ty, *t00, t1, super, false, soft)) {
                                        for (int i = 0; i < vN(t0->types); ++i) {
                                                if (v_(t0->types, i) != t00) {
                                                        type_subtract(ty, t00, v__(t0->types, i));
                                                }
                                        }
                                        goto Success;
                                }
                        }
                        goto Fail;
                } else {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                if (!UnifyXD(ty, v__(t0->types, i), t1, super, false, soft)) {
                                        goto Fail;
                                }
                        }
                        goto Success;
                }
        }

        if (TypeType(t1) == TYPE_UNION) {
                if (super) {
                        for (int i = 0; i < vN(t1->types); ++i) {
                                if (!UnifyXD(ty, t0, v__(t1->types, i), super, false, soft)) {
                                        goto Fail;
                                }
                        }
                        goto Success;
                } else {
                        for (int i = 0; i < vN(t1->types); ++i) {
                                if (UnifyXD(ty, t0, v__(t1->types, i), super, false, soft)) {
                                        goto Success;
                                }
                        }
                }
        }

        if (TypeType(t0) == TYPE_INTERSECT) {
                if (super) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                if (!UnifyXD(ty, v__(t0->types, i), t1, super, false, soft)) {
                                        goto Fail;
                                }
                        }
                        goto Success;
                } else {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                TypeEnv *env = NewEnv(ty, NULL);
                                if (
                                        UnifyXD(
                                                ty,
                                                NewInst0(ty, v__(t0->types, i), env),
                                                NewInst0(ty, t1,  env),
                                                super,
                                                false,
                                                soft
                                        )
                                ) {
                                        UnifyXD(
                                                ty,
                                                v__(t0->types, i),
                                                t1,
                                                super,
                                                false,
                                                soft
                                        );
                                        goto Success;
                                }
                        }
                        goto Fail;
                }
        }

        if (IsRecordLike(t0) || IsRecordLike(t1)) {
                if (TryUnifyObjects(ty, t0, t1, super)) {
                        goto Success;
                } else {
                        goto Fail;
                }
        }

        if (PackTypes(t0, t1) == PAIR_OF(TYPE_LIST)) {
                for (int i = 0; i < vN(t0->types) || i < vN(t1->types); ++i) {
                        Type *t0_ = ListItem(ty, t0, i, super ? ANY : NIL_TYPE);
                        Type *t1_ = ListItem(ty, t1, i, super ? NIL_TYPE : ANY);
                        if (!UnifyXD(ty, t0_, t1_, super, check, soft)) {
                                goto Fail;
                        }
                }
                goto Success;
        }

        if (TypeType(t0) == TYPE_CLASS) {
                t0 = ClassFunctionType(ty, t0);
        }

        if (TypeType(t1) == TYPE_CLASS) {
                t1 = ClassFunctionType(ty, t1);
        }

        if (TypeType(t0) == TYPE_TAG) {
                t0 = TagFunctionType(ty, t0);
        }

        if (TypeType(t1) == TYPE_TAG) {
                t1 = TagFunctionType(ty, t1);
        }

        if (TypeType(t0) == TYPE_FUNCTION && TypeType(t1) == TYPE_FUNCTION) {
                for (int i = 0; i < vN(t0->params) || i < vN(t1->params); ++i) {
                        Param const *p0 = (vN(t0->params) > i) ? v_(t0->params, i) : NULL;
                        Param const *p1 = (vN(t1->params) > i) ? v_(t1->params, i) : NULL;

                        Type *u0 = (p0 == NULL) ? NIL_TYPE : p0->type;
                        Type *u1 = (p1 == NULL) ? NIL_TYPE : p1->type;

                        if (
                                (p0 != NULL && (p0->kws || p0->rest))
                             || (p1 != NULL && (p1->kws || p1->rest))
                             || (super && p1 != NULL && !p1->required && IsNil(u0))
                             || (!super && p0 != NULL && !p0->required && IsNil(u1))
                        ) {
                                continue;
                        }

                        if (
                                !UnifyXD(ty, Inst1(ty, u0), Inst1(ty, u1), !super, false, soft)
                             && !UnifyXD(ty, Inst1(ty, u1), Inst1(ty, u0), super, false, soft)
                        ) {
                                goto Fail;
                        }
                }

                for (int i = 0; i < vN(t0->constraints); ++i) {
                        BindConstraint(ty, v_(t0->constraints, i), super);
                }

                for (int i = 0; i < vN(t1->constraints); ++i) {
                        BindConstraint(ty, v_(t1->constraints, i), super);
                }

                if (UnifyXD(ty, t0->rt, t1->rt, super, check, soft)) {
                        goto Success;
                } else {
                        goto Fail;
                }
        }

        bool ok;
        if (!type_check(ty, super ? t0 : t1, super ? t1 : t0)) {
Fail:
                ok = false;

        } else {
Success:
                ok = true;

                if (t0 != NULL && t1 != NULL) {
                        if (t0->src == NULL) t0->src = t1->src;
                        if (t1->src == NULL) t1->src = t0->src;
                }
        }

        d -= 1;
        vvX(visiting);

        XXTLOG("%s%s%s%s%s", color, line, ok ? TERM(92) : TERM(91), ok ? "OK" : "FAILED", TERM(0));

        DPRINT(
                false,
                "%s%sUnify%s(%s, %s):",
                ok ? TERM(92) : TERM(91),
                check ? "" : "Try",
                TERM(0),
                super ? "super" : "sub",
                soft ? "soft" : "hard"
        );
        DPRINT(true, "    %s", ShowType(t0));
        DPRINT(true, "    %s", ShowType(t1));

        if (ENFORCE && check && !ok) {
                type_check2(ty, super ? t1 : t0, super ? t0 : t1, true);
                TypeError(
                        "type mismatch"
                        FMT_MORE "found    (t0):  %s"
                        FMT_MORE "expected (t1):  %s"
                        FMT_MORE
                        FMT_MORE "t0 from:\n%s"
                        FMT_MORE "t1 from:\n%s",
                        ShowType(super ? t1 : t0),
                        ShowType(super ? t0 : t1),
                        trace(ty, super ? _t1 : _t0),
                        trace(ty, super ? _t0 : _t1)
                );
        }

        if (ok && FUEL > 0) {
                //FUEL = MAX_FUEL;
        }

        return ok;
#undef UnifyXD
}

static bool
UnifyX(Ty *ty, Type *t0, Type *t1, bool super, bool check)
{
        TLOG("UnifyX():");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s\n", ShowType(t1));

        bool ok = !CheckConstraints || UnifyXD(ty, t0, t1, super, false, false);

        if (!ok && check && ENFORCE) {
                EnableLogging += 1;
                UnifyXD(ty, t0, t1, super, false, false);
                EnableLogging -= 1;
                TypeError(
                        "type mismatch"
                        FMT_MORE "found    (t0):  %s"
                        FMT_MORE "expected (t1):  %s"
                        FMT_MORE
                        FMT_MORE "t0 from:%s"
                        FMT_MORE "t1 from:%s",
                        ShowType(super ? t1 : t0),
                        ShowType(super ? t0 : t1),
                        trace(ty, super ? t1 : t0),
                        trace(ty, super ? t0 : t1)
                );
        }

        return ok;
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
                break;

        case TC_EQ:
                //t0 = Propagate(ty, c->t0);
                //t1 = Propagate(ty, c->t1);
                //BindVars(ty, t1, t0, false);
                //BindVars(ty, t0, t1, check);
                XXTLOG("BindConstraint(=):");
                XXTLOG("    %s", ShowType(c->t0));
                XXTLOG("    %s", ShowType(c->t1));
                UnifyX(ty, c->t0, c->t1, true, false);
                XXTLOG("BindConstraint(=):");
                XXTLOG("    %s", ShowType(c->t0));
                XXTLOG("    %s", ShowType(c->t1));
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
        return;

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
                        //c->t0 = Propagate(ty, c->t0);
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
        TLOG("ResolveAlias(): t0=%s args=%d   params=%d", ShowType(t0), (int)vN(t0->args), (int)vN(t0->bound));
        if (CanResolveAlias(t0)) {
                return Inst(ty, t0->_type, &t0->bound, &t0->args);
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

        avP(f0->bound, v0->id);
        avP(f0->params, PARAM(NULL, v0, true));

        f0->rt = NewType(ty, TYPE_OBJECT);
        f0->rt->class = t0->class;
        avP(f0->rt->args, v0);

        t0->ft = f0;

        return f0;
}

static Type *
ClassFunctionType(Ty *ty, Type *t0)
{
        Type *t1 = Inst(ty, t0->class->object_type, &t0->class->type->bound, NULL);
        //Type *t1 = t0->class->object_type;

        //if (vN(t1->args) != vN(t0->class->type->bound)) {
        //        CloneVec(t1->args);
        //        while (vN(t1->args) != vN(t0->class->type->bound)) {
        //                avP(t1->args, NewVarOf(ty, v__(t0->class->type->bound, vN(t1->args))));
        //        }
        //}

        Type *t2 = type_member_access_t(ty, t1, "init", false);

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

        return Inst1(ty, t2);
        //return Generalize(ty, t2);
}

Type *
PossibleArgTypes(Ty *ty, expression_vector const *args, int argi)
{
        Type *t0 = NULL;

        for (int i = 0; i <= argi && i < vN(*args); ++i) {
                Expr const *arg = v__(*args, i);
                if (arg->type == EXPRESSION_SPREAD || i == argi) {
                        Type *arg0 = (arg->_type == NULL) ? UNKNOWN : arg->_type;
                        t0 = (t0 == NULL) ? arg0 : Either(ty, t0, arg0);
                }
        }

        return t0;
}

static Type *
FindArg(
        int i,
        char const *name,
        expression_vector const *args,
        expression_vector const *kwargs,
        StringVector const *kws
) {
        if (name != NULL) {
                for (int i = 0; i < vN(*kws); ++i) {
                        if (strcmp(v__(*kws, i), name) == 0) {
                                return v__(*kwargs, i)->_type;
                        }
                }
        }

        Type *t0 = (i != -1)
                 ? PossibleArgTypes(ty, args, i)
                 : NULL;

        return (t0 != NULL) ? t0 : NONE_TYPE;
}

static Param const *
FindParam(
        int argi,
        char const *name,
        ParamVector const *ps
) {
        if (name != NULL) {
                for (int i = 0; i < vN(*ps); ++i) {
                        Param const *p = v_(*ps, i);
                        if (p->name != NULL && strcmp(p->name, name) == 0) {
                                return p;
                        }
                }
        }

        for (int i = 0; i < vN(*ps); ++i) {
                Param const *p = v_(*ps, i);
                if (p->kws || name != NULL) {
                        if (p->kws && name != NULL) {
                                return p;
                        }
                } else if (p->rest || i == argi) {
                        return p;
                }
        }

        return NULL;
}

inline static bool
CheckArg(Ty *ty, int i, Param const *p, Type *a0, bool strict)
{
        Type *p0 = p->type;

        a0 = Inst1(ty, Unlist(ty, a0));

        if (
                strict
             && ENFORCE
             && a0 == NONE_TYPE
             && !type_check(ty, p0, NIL_TYPE)
        ) {
                if (p->name != NULL) {
                        TypeError(
                                "missing required argument for parameter %s%s%s of type `%s`",
                                TERM(93), p->name, TERM(0),
                                ShowType(p0)
                        );
                } else {
                        TypeError(
                                "missing required argument for parameter of type `%s`",
                                ShowType(p0)
                        );
                }
        }

        if (a0 == NONE_TYPE) {
                return false;
        }

        if (UnifyX(ty, p0, a0, true, false)) {
                return true;
        }

        ApplyConstraints(ty);

        if (UnifyX(ty, a0, p0, false, false)) {
                return true;
        }

        if (strict && ENFORCE) {
                //EnableLogging += 1;
                //UnifyX(ty, a0, p0, false, true);
                if (p->name != NULL) {
                        TypeError(
                                "invalid argument type for parameter %s%s%s:"
                                FMT_MORE "given:    %s"
                                FMT_MORE "expected: %s",
                                TERM(93), p->name, TERM(0),
                                ShowType(a0),
                                ShowType(p0)
                        );
                } else {
                        TypeError(
                                "invalid argument type for parameter %s%d%s:"
                                FMT_MORE "given:    %s"
                                FMT_MORE "expected: %s",
                                TERM(93), i, TERM(0),
                                ShowType(a0),
                                ShowType(p0)
                        );
                }
        }

        return false;
}

static Type *
InferCall0(
        Ty *ty,
        expression_vector const *args,
        expression_vector const *kwargs,
        StringVector const *kws,
        Type *t0,
        bool strict
)
{
        Type *t1;
        Type *t2;
        bool gather = false;

        vec(Expr) _argv = {0};
        expression_vector _args = {0};
        expression_vector _kwargs = {0};

        dont_printf("InferCall(%s)\n", ShowType(t0));
        for (int i = 0; i < vN(*args); ++i) {
                dont_printf("    %s\n", ShowType(v__(*args, i)->_type));
        }

        if (t0 == NULL) {
                return NULL;
        }

        switch (t0->type) {
        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
                        gather |= p->rest;
                        if (p->rest || p->kws) {
                                continue;
                        }
                        char const *name = p->name;
                        Type *a0 = FindArg(gather ? -1 : i, name, args, kwargs, kws);
                        if (a0 == NONE_TYPE && !p->required) {
                                continue;
                        }
                        if (!CheckArg(ty, i, p, a0, strict)) {
                                return NULL;
                        }
                }

                for (int i = 0; i < vN(*args); ++i) {
                        Param const *p = FindParam(i, NULL, &t0->params);
                        Type *a0 = v__(*args, i)->_type;
                        if (p != NULL && p->type != NULL) {
                                if (!CheckArg(ty, p - v_(t0->params, 0), p, a0, strict)) {
                                        return NULL;
                                }
                        } else if (ENFORCE && strict) {
                                TypeError(
                                        "argument %s%d%s of type %s%s%s has no matching parameter",
                                        TERM(92), i, TERM(0),
                                        TERM(93), ShowType(a0), TERM(0)
                                );
                        } else {
                                return NULL;
                        }
                }

                for (int i = 0; i < vN(*kws); ++i) {
                        if (strcmp(v__(*kws, i), "*") == 0) {
                                continue;
                        }
                        Param const *p = FindParam(i, v__(*kws, i), &t0->params);
                        Type *a0 = v__(*kwargs, i)->_type;
                        if (p != NULL && p->type != NULL) {
                                if (!CheckArg(ty, p - v_(t0->params, 0), p, a0, strict)) {
                                        return NULL;
                                }
                        } else if (ENFORCE && strict) {
                                TypeError(
                                        "keyword argument %s%s%s of type %s%s%s has no matching parameter",
                                        TERM(92), v__(*kws, i), TERM(0),
                                        TERM(93), ShowType(a0), TERM(0)
                                );
                        } else {
                                return NULL;
                        }
                }

                for (int i = 0; i < vN(t0->constraints); ++i) {
                        BindConstraint(ty, v_(t0->constraints, i), true);
                }

                return Reduce(ty, t0->rt);

        case TYPE_CLASS:
                return InferCall0(ty, args, kwargs, kws, ClassFunctionType(ty, t0), strict);

        case TYPE_TAG:
                if (vN(*args) > 1) {
                        t2 = NewType(ty, TYPE_TUPLE);
                        for (int i = 0; i < vN(*args); ++i) {
                                avP(t2->types, v__(*args, i)->_type);
                                avP(t2->names, NULL);
                        }
                } else if (vN(*kws) > 0) {
                        t2 = NewType(ty, TYPE_TUPLE);
                        for (int i = 0; i < vN(*kws); ++i) {
                                avP(t2->types, v__(*kwargs, i)->_type);
                                avP(t2->names, v__(*kws, i));
                        }
                } else {
                        t2 = (vN(*args) == 0) ? BOTTOM : v__(*args, 0)->_type;
                }
                dont_printf("argc=%d   nkw=%d   t2=%s\n", (int)vN(*args), (int)vN(*kws), ShowType(t2));
                t1 = NewType(ty, TYPE_OBJECT);
                t1->class = t0->class;
                avP(t1->args, t2);
                return t1;

        case TYPE_INTERSECT:
                XXTLOG("ResolveCall():");
                XXTLOG("  Args:");
                for (int i = 0; i < vN(*args); ++i) {
                        XXTLOG("   (%d) %s", i, ShowType(v__(*args, i)->_type));
                }

                XXTLOG("Overloads:");
                for (int i = 0; i < vN(t0->types); ++i) {
                        XXTLOG("  (%d) %s", i + 1, ShowType(v__(t0->types, i)));
                }

                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);

                        v0(_argv);
                        v0(_args);
                        v0(_kwargs);
                        Expr tmp = { .type = EXPRESSION_NIL };

                        TypeEnv *env = NewEnv(ty, NULL);

                        for (int i = 0; i < vN(*args); ++i) {
                                tmp._type = NewInst0(ty, v__(*args, i)->_type, env);
                                avP(_argv, tmp);
                        }

                        for (int i = 0; i < vN(*kwargs); ++i) {
                                tmp._type = NewInst0(ty, v__(*kwargs, i)->_type, env);
                                avP(_argv, tmp);
                        }

                        for (int i = 0; i < vN(*args); ++i) {
                                avP(_args, v_(_argv, i));
                        }

                        for (int i = 0; i < vN(*kwargs); ++i) {
                                avP(_kwargs, v_(_argv, i + vN(*args)));
                        }

                        t2 = NewInst(ty, t1);

                        Type *t3;
                        if ((t3 = InferCall0(ty, &_args, &_kwargs, kws, t2, false)) != NULL) {
                                XXTLOG(" OK:  %s", ShowType(t2));
                                XXTLOG("   -> %s", ShowType(t3));
                                return InferCall0(ty, args, kwargs, kws, t1, strict);
                        }
                }
                if (ENFORCE && strict) {
                        byte_vector msg = {0};
                        dump(&msg, FMT_MORE "Arguments:");
                        for (int i = 0; i < vN(*args); ++i) {
                                dump(&msg, FMT_MORE "  arg[%d]: %s", i, ShowType(v__(*args, i)->_type));
                        }
                        dump(&msg, FMT_MORE "Prototypes");
                        for (int i = 0; i < vN(t0->types); ++i) {
                                dump(&msg, FMT_MORE "  (%d) %s", i + 1, ShowType(v__(t0->types, i)));
                        }
                        TypeError("no matching prototype for given arguments%s", msg.items);
                }
        }

        return NULL;
}

static Type *
InferCall(
        Ty *ty,
        expression_vector const *args,
        expression_vector const *kwargs,
        StringVector const *kws,
        Type *t0
)
{
        return InferCall0(
                ty,
                args,
                kwargs,
                kws,
                t0,
                true
        );
}

static Type *
type_call_t(Ty *ty, Expr const *e, Type *t0)
{
        //XXTLOG("=== type_call(): %s", show_expr(e));

        if (IsBottom(t0)) {
                return t0;
        }

        if (IsNil(t0)) {
                return NIL_TYPE;
        }

        Type *t;
        Type *t1;
        expression_vector const *args = &(expression_vector){0};
        expression_vector const *kwargs = &(expression_vector){0};
        StringVector const *kws = &(StringVector){0};


        switch (e->type) {
        case EXPRESSION_FUNCTION_CALL:
                args = &e->args;
                kwargs = &e->kwargs;
                kws = &e->kws;
                break;
        case EXPRESSION_METHOD_CALL:
                args = &e->method_args;
                kwargs = &e->method_kwargs;
                kws = &e->method_kws;
                break;
        }

        switch (t0->type) {
        case TYPE_TAG:
                if ((vN(*args) == 1 && vN(*kws) == 0) || e->type == EXPRESSION_TAG_APPLICATION) {
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
                }

        case TYPE_FUNCTION:
        case TYPE_CLASS:
        case TYPE_INTERSECT:
                XXTLOG("Call(): %s", ShowType(t0));
                for (int i = 0; i < vN(*args); ++i) {
                        XXTLOG("   arg[%d] :: %s", i, ShowType(v__(*args, i)->_type));
                }
                return InferCall(ty, args, kwargs, kws, Inst1(ty, t0));


        case TYPE_UNION:
                t = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify2(ty, &t, type_call_t(ty, e, v__(t0->types, i)));
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
                        t1->rt->level = t0->level;
                        for (int i = 0; i < vN(*args); ++i) {
                                Type *p0 = NewVar(ty);
                                p0->level = t0->level;
                                avP(t1->params, PARAM(NULL, p0, true));
                        }
                        for (int i = 0; i < vN(*args); ++i) {
                                Unify(ty, v_(t1->params, i)->type, v__(*args, i)->_type, true);
                        }
                        Unify(ty, t1, t0, true);
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
                Expr *pat = v__(e->patterns, i);
                Expr *then = v__(e->thens, i);

                Type *p0 = NewVar(ty);
                Type *e0 = NewVar(ty);

                p0->src = pat;
                e0->src = then;

                type_assign(ty, pat, p0, false);
                UnifyX(ty, then->_type, e0, true, true);

                s0 = (s0 == NULL) ? p0 : Either(ty, s0, p0);
                t0 = (t0 == NULL) ? e0 : Either(ty, t0, e0);
        }

        if (TypeType(s0) == TYPE_UNION) {
                Type *s1 = NewVar(ty);
                for (int i = 0; i < vN(s0->types); ++i) {
                        Type *s00 = v__(s0->types, i);
                        if (CanBind(s00)) {
                                s1->level = min(s1->level, s00->level);
                                BindVar(s00, s1);
                        }
                }
                s0 = Reduce(ty, s0);
        }

        UnifyX(ty, e->subject->_type, s0, false, false);
        UnifyX(ty, s0, e->subject->_type, true, true);

        return t0;
}

Type *
type_match_stmt(Ty *ty, Stmt const *stmt)
{
        Type *t0 = NULL;
        Type *s0 = NULL;

        for (int i = 0; i < vN(stmt->match.patterns); ++i) {
                Expr *pat = v__(stmt->match.patterns, i);
                Stmt *then = v__(stmt->match.statements, i);

                Type *p0 = NewVar(ty);
                Type *e0 = NewVar(ty);

                p0->src = pat;
                e0->src = (Expr *)then;

                type_assign(ty, pat, p0, false);
                UnifyX(ty, then->_type, e0, true, true);

                s0 = (s0 == NULL) ? p0 : Either(ty, s0, p0);
                t0 = (t0 == NULL) ? e0 : Either(ty, t0, e0);
        }

        if (TypeType(s0) == TYPE_UNION) {
                Type *s1 = NewVar(ty);
                for (int i = 0; i < vN(s0->types); ++i) {
                        Type *s00 = v__(s0->types, i);
                        if (CanBind(s00)) {
                                s1->level = min(s1->level, s00->level);
                                BindVar(s00, s1);
                        }
                }
                s0 = Reduce(ty, s0);
        }

        UnifyX(ty, stmt->match.e->_type, s0, false, false);
        UnifyX(ty, s0, stmt->match.e->_type, true, true);

        return t0;
}

Type *
_type_match(Ty *ty, Expr const *e)
{
        Type *t0 = NULL;
        Type *s0 = NULL;

        for (int i = 0; i < e->patterns.count; ++i) {
                Expr *p = v__(e->patterns, i);
                Type *s00 = NULL;
                if (
                        p->type == EXPRESSION_LIST
                     || p->type == EXPRESSION_CHOICE_PATTERN
                ) {
                        s0 = NULL;
                        for (int j = 0; j < vN(p->es); ++j) {
                                Type *s000 = NewVar(ty);
                                type_assign(ty, v__(p->es, j), s00, false);
                                //unify2(ty, &s00, s000);
                                s00 = (s00 == NULL) ? s000 : Either(ty, s00, s000);
                        }
                } else {
                        if (IsFixed(e->subject->_type)) {
                                s00 = e->subject->_type;
                        } else {
                                s00 = NewVar(ty);
                        }
                        type_assign(ty, p, s00, false);
                }
                unify2(ty, &s0, s00);
        }

        UnifyX(ty, e->subject->_type, s0, true, false);
        UnifyX(ty, s0, e->subject->_type, false, true);

        for (int i = 0; i < e->patterns.count; ++i) {
                TLOG("match |= %s", ShowType(v__(e->thens, i)->_type));
                t0 = (t0 == NULL)
                   ? v__(e->thens, i)->_type
                   : Either(ty, t0, v__(e->thens, i)->_type);
                //unify2(ty, &t0, v__(e->thens, i)->_type);
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
FindGetter(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethod_(&c->def->class.getters, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindGetter(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

static Expr *
FindSetter(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethod_(&c->def->class.setters, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindSetter(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
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

static Type *
Inst0(Ty *ty, Type *t0, U32Vector const *params, TypeVector const *args, bool variadic)
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
                for (int i = 0; i < vN(*params) - variadic; ++i) {
                        avP(vars, NewHole(ty));
                }
                if (variadic) {
                        Type *rest0 = NewHole(ty);
                        rest0->variadic = true;
                        avP(vars, rest0);
                        variadic = false;
                }
                args = &vars;
        }

        TypeEnv *save = ty->tenv;
        ty->tenv = NewEnv(ty, NULL);

        for (int i = 0; i < vN(*params) - variadic && i < vN(*args); ++i) {
                TLOG("  %s := %s", VarName(ty, v__(*params, i)), ShowType(v__(*args, i)));
                PutEnv(ty, ty->tenv, v__(*params, i), v__(*args, i));
        }

        if (variadic) {
                Type *rest0 = NewType(ty, TYPE_SEQUENCE);
                for (int i = vN(*params) - variadic; i < vN(*args); ++i) {
                        avP(rest0->types, v__(*args, i));
                }
                PutEnv(ty, ty->tenv, *vvL(*params), rest0);
        }

        t0 = Propagate(ty, t0);

        ty->tenv = save;

        return t0;
}

static Type *
Inst(Ty *ty, Type *t0, U32Vector const *params, TypeVector const *args)
{
        return Inst0(ty, t0, params, args, t0 != NULL && t0->variadic);
}

static Type *
Inst1(Ty *ty, Type *t0)
{
        Type *t1 = t0;

        if (TypeType(t0) == TYPE_FUNCTION) {
                t1 = Inst0(ty, t0, &t0->bound, NULL, t0->variadic);
                if (t1 == t0) {
                        t1 = CloneType(ty, t1);
                }
                v00(t1->bound);
        } else if (TypeType(t0) == TYPE_OBJECT && !IsAny(t0)) {
                t1 = Inst0(ty, t0, &t0->class->type->bound, NULL, t0->variadic);
                if (t1 == t0) {
                        t1 = CloneType(ty, t1);
                }
                v00(t1->bound);
        } else if (TypeType(t0) == TYPE_INTERSECT) {
                t1 = CloneType(ty, t0);
                CloneVec(t1->types);
                for (int i = 0; i < vN(t1->types); ++i) {
                        *v_(t1->types, i) = Inst1(ty, v__(t1->types, i));
                }
        }

        XXTLOG("Inst1():");
        XXTLOG("    %s", ShowType(t0));
        XXTLOG("    %s\n", ShowType(t1));

        return t1;
}

static Type *
SolveMemberAccess(Ty *ty, Type const *t0, Type const *t1)
{
        t0 = Resolve(ty, t0);

        if (TypeType(t0) != TYPE_OBJECT || IsTagged(t0)) {
                return (Type *)t1;
        }

        Type *t = (Type *)t1;
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
                        &c->type->bound,
                        &t0->args
                );
                if (tr0 != NULL && tr0->class != NULL) {
                        t = Inst(
                                ty,
                                t,
                                &tr0->class->type->bound,
                                &tr0->args
                        );
                }
        }

        if (def->super != NULL) {
                Type *super0 = Inst(
                        ty,
                        type_resolve(ty, def->super),
                        &c->type->bound,
                        &t0->args
                );
                if (super0 != NULL && super0->class != NULL) {
                        t = Inst(
                                ty,
                                t,
                                &super0->class->type->bound,
                                &super0->args
                        );
                }
        }

        t = Inst(ty, t, &c->type->bound, &t0->args);
        //t = Inst1(ty, t);

        XXTLOG("SolveMemberAccess():");
        XXTLOG("    %s", ShowType(t0));
        XXTLOG("    %s", ShowType(t1));
        XXTLOG("    %s\n", ShowType(t));

        return t;
}

Type *
type_member_access_t_(Ty *ty, Type const *t0, char const *name, bool strict)
{
        TLOG("member_access(%s, %s)", ShowType(t0), name);

        t0 = Resolve(ty, t0);

        if (
                IsNil(t0)
             || IsBottom(t0)
             || IsAny(t0)
        ) {
                return (Type *)t0;
        }

        Class *c;
        Expr *f;

        Type *t1 = NULL;

        switch (TypeType(t0)) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        Type *t2 = type_member_access_t_(ty, v__(t0->types, i), name, false);
                        if (!IsBottom(t2)) {
                                unify2(ty, &t1, t2);
                        }
                }
                if (ENFORCE && strict && t1 == NULL) {
                        goto NotFound;
                }
                return t1;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        Type *t2 = type_member_access_t_(ty, v__(t0->types, i), name, false);
                        if (!IsBottom(t2)) {
                                type_intersect(ty, &t1, t2);
                        }
                }
                if (ENFORCE && strict && t1 == NULL) {
                        goto NotFound;
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
                if (t1 == NULL && strcmp(name, "__subscript__")) {
                }
                if (ENFORCE && strict && t1 == NULL) {
                        goto NotFound;
                }

                return t1;

        case TYPE_CLASS:
                c = t0->class;
                if (c->def == NULL) {
                        return UNKNOWN;
                }
                f = FindStatic(c, name);
                if (f != NULL) {
                        t1 = f->_type;

                }
                if (t1 == NULL) {
                        f = FindMethod(c, name);
                        if (f != NULL) {
                                t1 = f->_type;
                        }
                }
                if (ENFORCE && strict && t1 == NULL) {
                        goto NotFound;
                }
                return SolveMemberAccess(ty, t0, t1);

        case TYPE_OBJECT:
                if (IsTagged(t0)) {
                        if (ENFORCE && strict) {
                                goto NotFound;
                        } else {
                                return BOTTOM;
                        }
                }
                c = t0->class;
                if (c->def == NULL) {
                        return UNKNOWN;
                }
                f = FindField(c, name);
                if (f != NULL) {
                        t1 = f->_type;
                }
                if (t1 == NULL) {
                        f = FindMethod(c, name);
                        if (f != NULL) {
                                t1 = f->_type;
                        }
                }
                if (t1 == NULL) {
                        f = FindGetter(c, name);
                        if (f != NULL) {
                                if (TypeType(f->_type) == TYPE_FUNCTION) {
                                        t1 = f->_type->rt;
                                }
                        }
                }
                if (t1 == NULL) {
                        f = FindSetter(c, name);
                        if (f != NULL) {
                                t1 = f->_type;
                        }
                }
                if (t1 == NULL) switch (c->i) {
                case CLASS_ARRAY:
                        if (get_array_method(name) != NULL) {
                                t1 = UNKNOWN;
                        }
                        break;
                case CLASS_STRING:
                        if (get_string_method(name) != NULL) {
                                t1 = UNKNOWN;
                        }
                        break;
                case CLASS_DICT:
                        if (get_dict_method(name) != NULL) {
                                t1 = UNKNOWN;
                        }
                        break;
                case CLASS_BLOB:
                        if (get_blob_method(name) != NULL) {
                                t1 = UNKNOWN;
                        }
                        break;
                }
                if (ENFORCE && strict && t1 == NULL) {
                        goto NotFound;
                }
                return SolveMemberAccess(ty, t0, t1);

        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        return type_member_access_t_(ty, t0->val, name, strict);
                } else if (!IsTVar(t0)) {
                        t1 = NewType(ty, TYPE_TUPLE);
                        avP(t1->names, name);
                        avP(t1->types, NewVar(ty));
                        Unify(ty, (Type *)t0, t1, true);
                        return *vvL(t1->types);
                } else {
                        return NULL;
                }
        }

        return t1;

NotFound:
        TypeError("field `%s` does not exist on `%s`", name, ShowType(t0));
}

Type *
type_member_access_t(Ty *ty, Type const *t0, char const *name, bool strict)
{
        Type *t1 = type_member_access_t_(ty, t0, name, strict);
        TLOG("MemberAccess(%s):", name);
        TLOG("  t0:  %s", ShowType(t0));
        TLOG("  t1:  %s\n", ShowType(t1));
        return t1;
}

Type *
type_member_access(Ty *ty, Expr const *e)
{
        if (!ENABLED) {
                return UNKNOWN;
        }

        if (e->type == EXPRESSION_DYN_MEMBER_ACCESS) {
                return NewVar(ty);
        }

        Type *t0 = type_member_access_t(ty, e->object->_type, e->member_name, false);
        Type *t1;

        if (t0 == NULL) {
                if (e->maybe) {
                        return NIL_TYPE;
                } else if (!IsFixed(e->object->_type)) {
                        t0 = NewVar(ty);
                        t1 = NewType(ty, TYPE_TUPLE);
                        avP(t1->names, e->member_name);
                        avP(t1->types, t0);
                        type_intersect(ty, &e->object->_type, t1);
                } else {
                        type_member_access_t(ty, e->object->_type, e->member_name, true);
                }
        }

        return t0;
}

Type *
type_method_call_t(Ty *ty, Expr const *e, Type *t0, char const *name)
{
        t0 = Resolve(ty, t0);

        if (IsNil(t0)) {
                return NIL_TYPE;
        }

        if (IsAny(t0) || IsBottom(t0)) {
                return t0;
        }

        if (e->type == EXPRESSION_DYN_METHOD_CALL) {
                return BOTTOM;
        }

        Type *t1;
        Type *t2;

        switch (t0->type) {
        case TYPE_OBJECT:
                t1 = type_member_access_t(ty, t0, name, false);
                dont_printf("%s.%s() :: %s\n", t0->class->name, name, ShowType(t1));
        case TYPE_CLASS:
        case TYPE_VARIABLE:
        case TYPE_TUPLE:
                t1 = SolveMemberAccess(ty, t0, type_member_access_t(ty, t0, name, false));
                t1 = Inst(ty, t1, &t0->bound, NULL);
                t1 = SolveMemberAccess(ty, t0, type_call_t(ty, e, t1));
                return t1;

        case TYPE_UNION:
                t1 = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify2(ty, &t1, type_method_call_t(ty, e, v__(t0->types, i), name));
                }
                return t1;

        case TYPE_INTERSECT:
                t1 = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        t2 = type_method_call_t(ty, e, v__(t0->types, i), name);
                        if (!IsBottom(t2)) {
                                type_intersect(ty, &t1, t2);
                        }
                }
                return t1;
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

        t1->concrete = IsConcrete(t0);

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
type_slice_t(Ty *ty, Type *t0, Type *t1, Type *t2, Type *t3)
{
        Type *t4 = NewVar(ty);
        Type *t5 = NewRecord("__slice__", NewFunction(t1, t2, t3, t4));

        UnifyX(ty, t5, t0, false, false)
     || UnifyX(ty, t0, t5, false, true);

        return t4;
}

Type *
type_subscript_t(Ty *ty, Type *t0, Type *t1)
{
        Type *t2 = NewVar(ty);
        Type *t3 = NewRecord("__subscript__", NewFunction(t1, t2));

        UnifyX(ty, t0, t3, true, false)
     || UnifyX(ty, t3, t0, true, true);

        return t2;
}

static Type *
SubscriptType(Ty *ty, Type *t0, Type *t1)
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
                        unify2(ty, &t2, SubscriptType(ty, v__(t0->types, i), t1));
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

Type *
type_slice(Ty *ty, Expr const *e)
{
        return type_slice_t(
                ty,
                e->slice.e->_type,
                ExprTypeOr(e->slice.i, NIL_TYPE),
                ExprTypeOr(e->slice.j, NIL_TYPE),
                ExprTypeOr(e->slice.k, NIL_TYPE)
        );
}

static bool
check_entry(Ty *ty, Type *t0, int i, Type *t1, bool need)
{
        if (IsBottom(t0)) {
                return false;
        }

        switch (t0->type) {
        case TYPE_UNION:
                for (int ii = 0; ii < vN(t0->types); ++ii) {
                        if (!check_entry(ty, v__(t0->types, ii), i, t1, need)) {
                                return false;
                        }
                }
                return true;

        case TYPE_INTERSECT:
                for (int ii = 0; ii < vN(t0->types); ++ii) {
                        if (check_entry(ty, v__(t0->types, ii), i, t1, false)) {
                                return true;
                        }
                }
                return false;

        case TYPE_TUPLE:
                return vN(t0->types) > i
                    && type_check_x(ty, v__(t0->types, i), t1, need);
        }

        return false;
}

static bool
check_field(Ty *ty, Type *t0, char const *name, Type *t1, bool need)
{
        t0 = ResolveVar(t0);

        if (IsBottom(t0)) {
                return false;
        }

        Type *t2;
        Expr const *m;

        switch (t0->type) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!check_field(ty, v__(t0->types, i), name, t1, need)) {
                                return false;
                        }
                }
                return true;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (check_field(ty, v__(t1->types, i), name, t1, false)) {
                                return true;
                        }
                }
                return false;

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
                                return type_check_x(ty, v__(t0->types, i), t1, need);
                        }
                }
                return false;

        case TYPE_OBJECT:
                t2 = type_member_access_t_(ty, t0, name, false);
                if (t2 != NULL) {
                        return type_check_x(ty, t2, t1, need);
                }
        }

        return false;
}

static int d = 0;

static bool
type_check_shallow(Ty *ty, Type *t0, Type *t1)
{
        if (
                IsAny(t0)
             || SameType(t0, t1)
             || IsBottom(t1)
             || IsBottom(t0)
        ) {
                return true;
        }

        Type *t0_ = Resolve(ty, t0);
        Type *t1_ = Resolve(ty, t1);

        if (t0_ != t0 || t1_ != t1) {
                t0 = t0_;
                t1 = t1_;
                if (
                        IsAny(t0)
                     || SameType(t0, t1)
                     || IsBottom(t1)
                     || IsBottom(t0)
                ) {
                        return true;
                }
        }

        Flatten(ty, t0);
        Flatten(ty, t1);

        if (IsAny(t1)) {
                return false;
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

        return false;
}

bool
type_check_x_(Ty *ty, Type *t0, Type *t1, bool need)
{
        if (
                IsAny(t0)
             || SameType(t0, t1)
             || IsBottom(t1)
             || IsBottom(t0)
        ) {
                return true;
        }

        Type *t0_ = Resolve(ty, t0);
        Type *t1_ = Resolve(ty, t1);

        if (t0_ != t0 || t1_ != t1) {
                t0 = t0_;
                t1 = t1_;
                if (
                        IsAny(t0)
                     || SameType(t0, t1)
                     || IsBottom(t1)
                     || IsBottom(t0)
                ) {
                        return true;
                }
        }

        Flatten(ty, t0);
        Flatten(ty, t1);

        if (IsAny(t1)) {
                return false;
        }

        if (IsComputed(t0) || IsComputed(t1)) {
                return false;
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
                        if (!type_check_x(ty, t0, v__(t1->types, i), need)) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_SEQUENCE && t1->type == TYPE_SEQUENCE) {
                if (vN(t0->types) != vN(t1->types)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (
                                !type_check_x(
                                        ty,
                                        v__(t0->types, i),
                                        v__(t1->types, i),
                                        need)
                        ) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_LIST && t1->type == TYPE_LIST) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        Type *t0_ = v__(t0->types, i);
                        Type *t1_ = (i < vN(t1->types)) ? v__(t1->types, i) : NIL_TYPE;
                        if (!type_check_x(ty, t0_, t1_, need)) {
                                return false;
                        }
                }
                return true;
        }

        if (t1->type == TYPE_LIST) {
                return type_check_x(ty, t0, NthType(t1, 0), need);
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
                                                false
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

        t0 = Relax(t0);
        t1 = Relax(t1);

        if (t1->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (type_check_x(ty, t0, v__(t1->types, i), false)) {
                                return true;
                        }
                }
                return false;
        }

        if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        if (!type_check_x(ty, t0, v__(t1->types, i), need)) {
                                return false;
                        }
                }
                return true;
        }

        if (t0->type == TYPE_UNION) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (type_check_x(ty, v__(t0->types, i), t1, need)) {
                                return true;
                        }
                }
                return false;
        }

        if (t0->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!type_check_x(ty, v__(t0->types, i), t1, need)) {
                                return false;
                        }
                }
                return true;
        }

        if (t1->type == TYPE_OBJECT && t1->class->def != NULL) {
                ClassDefinition *def = &t1->class->def->class;
                for (int i = 0; i < vN(def->traits); ++i) {
                        Type *trait0 = SolveMemberAccess(
                                ty,
                                t1,
                                type_resolve(ty, v__(def->traits, i))
                        );
                        if (
                                !IsBottom(trait0)
                             && type_check_x(
                                        ty,
                                        t0,
                                        trait0,
                                        false
                                )
                        ) {
                                return true;
                        }
                }
                if (def->super != NULL) {
                        Type *super0 = SolveMemberAccess(
                                ty,
                                t1,
                                type_resolve(ty, def->super)
                        );
                        if (
                                !IsBottom(super0)
                             && type_check_x(ty, t0, super0, false)
                        ) {
                                return true;
                        }
                }
        }

        if (t0->type == TYPE_TUPLE) {
                if (!IsRecordLike(t1)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->types); ++i) {
                        char const *name = v__(t0->names, i);
                        Type *t2 = (name != NULL)
                                 ? RecordField(ty, t1, name)
                                 : RecordElem(t1, i);
                        if (t2 == NULL) {
                                t2 = NIL_TYPE;
                        }
                        if (!type_check_x(ty, v__(t0->types, i), t2, need)) {
                                DPRINT(name && need, "Field(%s) %s != %s", name, ShowType(v__(t0->types, i)), ShowType(t2));
                                DPRINT(!name && need, "Field(%d) %s != %s", i, ShowType(v__(t0->types, i)), ShowType(t2));
                                return false;
                        }
                }
                return true;
        }

        if (t1->type == TYPE_TUPLE) {
                if (!IsRecordLike(t0)) {
                        return false;
                }
                for (int i = 0; i < vN(t1->types); ++i) {
                        char const *name = v__(t1->names, i);
                        if (
                                name == NULL
                              ? !check_entry(ty, t0, i, v__(t1->types, i), need)
                              : !check_field(ty, t0, name, v__(t1->types, i), need)
                        ) {
                                DPRINT(name && need, "Field(%s) %s.%s != %s", name, ShowType(t0), name, ShowType(v__(t1->types, i)));
                                DPRINT(!name && need, "Field(%d) %s.%d != %s", i, ShowType(t0), i, ShowType(v__(t1->types, i)));
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
                     && c0 >= CLASS_OBJECT
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
                                        need
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
                t1 = Inst1(ty, TagFunctionType(ty, t1));
                v_(t1->params, 0)->type = (vN(t0->params) > 0)
                                            ? v_(t0->params, 0)->type
                                            : UNKNOWN;
        }

        if (t1->type == TYPE_FUNCTION && t0->type == TYPE_TAG) {
                t0 = Inst1(ty, TagFunctionType(ty, t0));
                v_(t0->params, 0)->type = (vN(t1->params) > 0)
                                            ? v_(t1->params, 0)->type
                                            : UNKNOWN;
        }

        if (t0->type == TYPE_FUNCTION && t1->type == TYPE_FUNCTION) {
                //TypeEnv *env = NewEnv(ty, NULL);
                //t0 = NewInst0(ty, t0, env);
                //t1 = NewInst0(ty, t1, env);
                for (int i = 0; i < vN(t0->params) && i < vN(t1->params); ++i) {
                        Param const *pp0 = v_(t0->params, i);
                        Param const *pp1 = v_(t1->params, i);
                        if (
                                (pp0->rest ^ pp1->rest)
                             || (pp0->kws ^ pp1->kws)
                        ) {
                                continue;
                        }
                        Type *p0 = pp0->type;
                        Type *p1 = pp1->type;
                        //UnifyX(ty, p0, p1, false, false);
                        //UnifyX(ty, p1, p0, true, false);
                        if (!type_check_x(ty, p1, p0, need)) {
                                return false;
                        }
                }
                for (int i = vN(t1->params); i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
                        if (p->required && !p->kws && !p->rest) {
                                return false;
                        }
                }
                //ApplyConstraints(ty);
                Type *r0 = t0->rt;
                Type *r1 = t1->rt;
                //UnifyX(ty, r0, r1, true, false);
                //UnifyX(ty, r1, r0, false, false);
                if (!type_check_x(ty, r0, r1, need)) {
                        return false;
                } else {
                        return true;
                }
        }

        return false;
}

static u32 checks = 0;

bool
type_check_x(Ty *ty, Type *t0, Type *t1, bool need)
{
        checks += 1;
        d += 1;
        bool ok = type_check_x_(ty, t0, t1, need);
        d -= 1;
        if (!ok && need) {
                XXTLOG("%stype_check_x():%s", ok ? TERM(92) : TERM(91), TERM(0));
                XXTLOG("    %s", ShowType(t0));
                XXTLOG("    %s", ShowType(t1));
        } else {
                TLOG("%stype_check_x():%s", ok ? TERM(92) : TERM(91), TERM(0));
                TLOG("    %s", ShowType(t0));
                TLOG("    %s", ShowType(t1));
        }
        return ok;
}

static bool
type_check2(Ty *ty, Type *t0, Type *t1, bool need)
{
        static TypeMemo memo;

        checks = 0;

        bool ok;
        if (CheckMemo(&memo, t0, t1, &ok)) {
                XXTLOG("type_check():");
                XXTLOG("    %s", ShowType(t0));
                XXTLOG("    %s", ShowType(t1));
                XXTLOG(" => %s\n", ok ? "true" : "false");
                return ok;
        }

        ok = type_check_x(ty, t0, t1, need);

        ///XXTLOG("type_check():");
        ///XXTLOG("    %s", ShowType(t0));
        ///XXTLOG("    %s", ShowType(t1));
        ///XXTLOG(" => %s\n", ok ? "true" : "false");

        if (checks > 8 && IsConcrete(t0) && IsConcrete(t1)) {
                AddMemo(&memo, t0, t1, ok);
        }

        return ok;
}

bool
type_check(Ty *ty, Type *t0, Type *t1)
{
        static TypeMemo memo;

        if (!FuelCheck()) {
                return false;
        }

        if (SameType(t0, t1)) {
                return true;
        }

        checks = 0;

        bool ok;
        if (false && CheckMemo(&memo, t0, t1, &ok)) {
                return ok;
        }

        TLOG("type_check():");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s", ShowType(t1));

        ok = !CheckConstraints || type_check_x(ty, t0, t1, false);

        if (false && checks > 8 && IsConcrete(t0) && IsConcrete(t1)) {
                AddMemo(&memo, t0, t1, ok);
        }

        return ok;
}

Type *
type_tuple(Ty *ty, Expr const *e)
{
        Type *t0 = NewType(ty, TYPE_TUPLE);

        for (int i = 0; i < vN(e->es); ++i) {
                Type *u0 = NewVar(ty);
                avP(t0->types, u0);
                avP(t0->names, v__(e->names, i));
                BindVar(u0, (v__(e->es, i)->_type));
        }

        return t0;
}

Type *
type_list(Ty *ty, Expr const *e)
{
        Type *t0 = NewType(ty, TYPE_LIST);

        for (int i = 0; i < vN(e->es); ++i) {
                avP(t0->types, Relax(v__(e->es, i)->_type));
        }

        return t0;
}

Type *
type_list_from(Ty *ty, expression_vector const *es)
{
        Type *t0 = NewType(ty, TYPE_LIST);

        for (int i = 0; i < vN(*es); ++i) {
                avP(t0->types, v__(*es, i)->_type);
        }

        return t0;
}

Type *
type_list_item(Ty *ty, Type const *t0, int i)
{
        return ListItem(ty, t0, i, NIL_TYPE);
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
        Type *t0 = NewVar(ty);
        Type *t1 = NewVar(ty);

        for (int i = 0; i < vN(e->keys); ++i) {
                unify2(ty, &t0, v__(e->keys, i)->_type);
                unify2(
                        ty,
                        &t1,
                        (v__(e->values, i) == NULL) ? NIL_TYPE : v__(e->values, i)->_type
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

        Type *t = NewType(ty, TYPE_OBJECT);
        t->class = class_get_class(ty, CLASS_ARRAY);
        avP(t->args, t1);

        return t;
}

Type *
type_array(Ty *ty, Expr const *e)
{
        Type *t0 = NewVar(ty);
        Type *t1;

        if (vN(e->elements) == 1) {
                Unify(ty, t0, v__(e->elements, 0)->_type, true);
        } else if (vN(e->elements) > 1) {
                t1 = NewType(ty, TYPE_UNION);
                for (int i = 0; i < vN(e->elements); ++i) {
                        Type *u0 = v__(e->elements, i)->_type;
                        avP(t1->types, u0);
                }
                Unify(ty, t0, Reduce(ty, t1), true);
        }

        return NewObject(CLASS_ARRAY, t0);
}

static Type *
ListItem(Ty *ty, Type const *t0, int idx, Type const *alt)
{
        Type *t1;
        Type *t2;
        Type *t3;
        bool cloned = false;

        t0 = ResolveVar(t0);

        switch (TypeType(t0)) {
        case TYPE_LIST:
                t1 = (idx < vN(t0->types)) ? v__(t0->types, idx) : (Type *)alt;
                break;

        case TYPE_UNION:
        case TYPE_INTERSECT:
                t1 = (Type *)t0;
                for (int i = 0; i < vN(t1->types); ++i) {
                        t2 = v__(t0->types, i);
                        t3 = ListItem(ty, t2, idx, alt);
                        if (t3 != t2 && !cloned) {
                                t1 = CloneType(ty, t1);
                                CloneVec(t1->types);
                                cloned = true;
                        }
                        *v_(t1->types, i) = t3;
                }
                t1 = Reduce(ty, t1);
                break;

        default:
                t1 = (idx == 0) ? (Type *)t0 : (Type *)alt;
                break;
        }

        return t1;
}

void
type_assign(Ty *ty, Expr *e, Type *t0, int flags)
{
        XXTLOG("assign(%s)", flags ? "flags" : "");
        XXTLOG("    %s", ShowType(t0));
        XXTLOG("    %s\n", show_expr(e));

        Type *t1;
        Type *t2;
        Type *t3;
        Type *t4;

        //t0 = Resolve(ty, t0);

        if (t0 == NULL) {
                t0 = NewVar(ty);
                t0->src = e;
        }

        if (
                e->type != EXPRESSION_LIST
             && e->type != EXPRESSION_CHOICE_PATTERN
        ) {
                t0 = Unlist(ty, t0);
        }

        switch (e->type) {
        case EXPRESSION_MATCH_NOT_NIL:
                t0 = type_not_nil(ty, t0);
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_RESOURCE_BINDING:
                if (!e->symbol->fixed) {
                        XXTLOG(
                                "type_assign(): %s : %s |= %s",
                                e->symbol->identifier,
                                ShowType(e->symbol->type),
                                ShowType(t0)
                        );
                        if (flags & T_FLAG_UPDATE) {
                                Refinement *ref = ScopeRefineVar(
                                        ty,
                                        TyCompilerState(ty)->active,
                                        e->symbol,
                                        t0
                                );
                                ref->mut = true;
                        } else {
                                unify2(ty, &e->symbol->type, t0);
                        }
                        unify2(ty, &e->_type, t0);
                        XXTLOG(
                                "type_assign(): %s |= %s    --->    %s",
                                e->symbol->identifier,
                                ShowType(t0),
                                ShowType(e->symbol->type)
                        );
                } else if (
                        !UnifyX(ty, t0, e->symbol->type, false, false)
                     && (flags & T_FLAG_STRICT)
                     && ENFORCE
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
                t1 = NewVar(ty);
                Unify(ty, t0, type_tagged(ty, e->symbol->tag, t1), true);
                type_assign(ty, e->tagged, t1, flags);
                break;
        case EXPRESSION_ARRAY:
                t1 = NULL;
                for (int i = 0; i < vN(e->elements); ++i) {
                        t2 = NewVar(ty);
                        t1 = (t1 == NULL) ? t2 : Either(ty, t1, t2);
                        type_assign(ty, v__(e->elements, i), t2, flags);
                }
                UnifyX(ty, NewObject(CLASS_ARRAY, t1), t0, true, true);
                break;
        case EXPRESSION_TUPLE:
                t1 = NewType(ty, TYPE_TUPLE);
                for (int i = 0; i < vN(e->es); ++i) {
                        char const *name = v__(e->names, i);
                        if (name != NULL && strcmp(name, "*") == 0) {
                                continue;
                        }
                        if (v__(e->required, i)) {
                                t2 = NewVar(ty);
                        } else {
                                t2 = NewForgivingVar(ty);
                        }
                        avP(t1->names, name);
                        avP(t1->types, t2);
                        type_assign(ty, v__(e->es, i), t2, flags);
                }
                Unify(ty, t1, t0, true);
                break;
        case EXPRESSION_DICT:
                t1 = NewVar(ty);
                t2 = NewVar(ty);
                t3 = NewObject(CLASS_DICT, t1, t2);
                for (int i = 0; i < vN(e->keys); ++i) {
                        Expr *key = v__(e->keys, i);
                        Expr *val = v__(e->values, i);
                        t4 = NewVar(ty);
                        type_assign(ty, val, t4, flags);
                        unify2(ty, &t1, key->_type);
                        unify2(ty, &t2, t4);
                }
                UnifyX(ty, t0, t3, true, true);
                break;

        case EXPRESSION_CHOICE_PATTERN:
                t1 = NULL;
                for (int i = 0; i < vN(e->es); ++i) {
                        Type *var = NewVar(ty);
                        type_assign(ty, v__(e->es, i), var, flags);
                        t1 = (t1 == NULL) ? var : Either(ty, t1, var);
                }
                UnifyX(ty, t0, t1, true, true);
                break;
        case EXPRESSION_LIST:
                t0 = Resolve(ty, t0);
                for (int i = 0; i < vN(e->es); ++i) {
                        type_assign(
                                ty,
                                v__(e->es, i),
                                ListItem(ty, t0, i, NIL_TYPE),
                                flags
                        );
                }
                break;
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                t0 = type_not_nil(ty, t0);
        case EXPRESSION_VIEW_PATTERN:
                t1 = NewVar(ty);
                t2 = NewVar(ty);
                t3 = NewFunction(t1, t2);
                type_assign(ty, e->right, t2, flags);
                UnifyX(ty, t3, Inst1(ty, e->left->_type), true, true);
                UnifyX(ty, t1, t0, true, true);
                break;

        case EXPRESSION_MEMBER_ACCESS:
                t1 = NewForgivingVar(ty);
                t2 = NewRecord(e->member_name, t1);
                Unify(ty, e->object->_type, t2, true);
                Unify(ty, t1, t0, true);
                break;
        }
}

Type *
type_inst(Ty *ty, Type const *t0)
{
        return Inst1(ty, (Type *)t0);
}

Type *
type_inst0(Ty *ty, Type const *t0, U32Vector const *params, TypeVector const *args)
{
        return Inst0(ty, (Type *)t0, params, args, false);
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

        bool variadic = false;

        switch (e->type) {
        case EXPRESSION_MATCH_REST:
                variadic = true;
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
                        } else if (SymbolIsTypeVar(e->symbol)) {
                                return e->symbol->type;
                        } else {
                                t0 = BOTTOM;
                        }
                }
                if (t0 != NULL && t0->variadic != variadic) {
                        t0 = CloneType(ty, t0);
                        t0->variadic = variadic;
                }
                dont_printf("resolve(id): %s -> %s\n", e->identifier, ShowType(t0));
                return t0;

        case EXPRESSION_LIST:
                t0 = NewType(ty, TYPE_SEQUENCE);
                for (int i = 0; i < vN(e->es); ++i) {
                        avP(t0->types, type_resolve(ty, v__(e->es, i)));
                }
                return t0;

        case EXPRESSION_MATCH_ANY:
                return type_fixed(ty, UNKNOWN);

        case EXPRESSION_TYPEOF:
                return e->operand->_type;

        case EXPRESSION_TYPE:
                return e->_type;

        case EXPRESSION_SPREAD:
                t0 = type_resolve(ty, e->value);
                if (t0 != NULL && !t0->variadic) {
                        t0 = CloneType(ty, t0);
                        t0->variadic = true;
                }
                return t0;

        case EXPRESSION_SUBSCRIPT:
                t0 = CloneType(ty, type_resolve(ty, e->container));
                if (IsTVar(t0) && e->subscript->type == EXPRESSION_INTEGER) {
                        t1 = NewType(ty, TYPE_SUBSCRIPT);
                        t1->i = e->subscript->integer;
                        t1->val = t0;
                        t0 = t1;
                } else if (IsTVar(t0) && e->subscript->type == EXPRESSION_DOT_DOT) {
                        Type *i0 = type_resolve(ty, e->subscript->left);
                        Type *j0 = type_resolve(ty, e->subscript->right);
                        t1 = NewType(ty, TYPE_SLICE);
                        t1->i = (TypeType(i0) == TYPE_INTEGER) ? i0->z : 0;
                        t1->j = (TypeType(j0) == TYPE_INTEGER) ? j0->z : INT_MAX;
                        t1->k = 1;
                        t1->val = t0;
                        t0 = t1;
                } else if (t0 != NULL) {
                        t1 = type_resolve(ty, e->subscript);
                        if (
                                TypeType(t1) == TYPE_SEQUENCE
                             || TypeType(t1) == TYPE_LIST
                        ) {
                                t0->args = t1->types;
                        } else {
                                CloneVec(t0->args);
                                avP(t0->args, t1);
                        }
                        if (t0->type == TYPE_TAG) {
                                t0->type = TYPE_OBJECT;
                        }
                        t0->concrete &= (t1 == NULL || t1->concrete) && (TypeType(t0) != TYPE_ALIAS || t0->_type != NULL);
                }
                dont_printf("resolve_subscript():\n");
                dont_printf("%s\n", show_expr(e));
                dont_printf("  -> %s\n", ShowType(t0));
                return t0;

        case EXPRESSION_SLICE:
                t0 = CloneType(ty, type_resolve(ty, e->slice.e));
                XXTLOG("slice(): t0 = %s", ShowType(t0));
                if (IsTVar(t0)) {
                        Type *i0 = type_resolve(ty, e->slice.i);
                        Type *j0 = type_resolve(ty, e->slice.j);
                        Type *k0 = type_resolve(ty, e->slice.k);
                        XXTLOG("slice(): i = %s", ShowType(i0));
                        XXTLOG("slice(): j = %s", ShowType(j0));
                        XXTLOG("slice(): k = %s", ShowType(k0));
                        t1 = NewType(ty, TYPE_SLICE);
                        t1->k = (TypeType(k0) == TYPE_INTEGER) ? (k0->z + !k0->z) : 1;
                        t1->i = (TypeType(i0) == TYPE_INTEGER) ? i0->z : 0;
                        t1->j = (TypeType(j0) == TYPE_INTEGER) ? j0->z : (t1->k < 0) ? 0 : INT_MAX;
                        t1->val = t0;
                        t0 = t1;
                }
                dont_printf("resolve_slice(): -> %s\n", ShowType(t0));
                return t0;

        case EXPRESSION_TUPLE:
                t0 = NewType(ty, TYPE_TUPLE);
                t0->concrete = true;
                for (int i = 0; i < vN(e->es); ++i) {
                        avP(t0->names, v__(e->names, i));
                        avP(t0->types, type_resolve(ty, v__(e->es, i)));
                }
                return t0;

        case EXPRESSION_TYPE_UNION:
                t0 = NewType(ty, TYPE_UNION);
                for (int i = 0; i < vN(e->es); ++i) {
                        t1 = type_resolve(ty, v__(e->es, i));
                        avP(t0->types, type_unfixed(ty, t1));
                }
                return Reduce(ty, t0);

        case EXPRESSION_BIT_OR:
                t0 = type_unfixed(ty, type_resolve(ty, e->left));
                t1 = type_unfixed(ty, type_resolve(ty, e->right));
                t2 = Either(ty, t0, t1);
                XXTLOG("resolve(|):");
                XXTLOG("  %s", ShowType(t0));
                XXTLOG("  %s", ShowType(t1));
                XXTLOG("  %s\n", ShowType(t2));
                return t2;

        case EXPRESSION_BIT_AND:
                t0 = type_unfixed(ty, type_resolve(ty, e->left));
                t1 = type_unfixed(ty, type_resolve(ty, e->right));
                if (type_check(ty, t0, t1)) {
                        return t1;
                }
                if (type_check(ty, t1, t0)) {
                        return t0;
                }
                t2 = NewType(ty, TYPE_INTERSECT);
                avP(t2->types, t0);
                avP(t2->types, t1);
                return t2;

        case EXPRESSION_PREFIX_QUESTION:
                t0 = type_resolve(ty, e->operand);
                return Either(ty, t0, NIL_TYPE);

        case EXPRESSION_FUNCTION_CALL:
                t0 = NewType(ty, TYPE_COMPUTED);
                t0->func = compiler_eval(ty, e->function);
                for (int i = 0; i < vN(e->args); ++i) {
                        avP(t0->args, type_resolve(ty, v__(e->args, i)));
                }
                return t0;

        case EXPRESSION_FUNCTION:
                return NULL;

        case EXPRESSION_FUNCTION_TYPE:
                t0 = NewType(ty, TYPE_FUNCTION);
                if (e->left->type == EXPRESSION_LIST) {
                        for (int i = 0; i < vN(e->left->es); ++i) {
                                avP(
                                        t0->params,
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
                                char const *name = (vN(e->left->names) > i)
                                                 ? v__(e->left->names, i)
                                                 : NULL;
                                avP(
                                        t0->params,
                                        PARAM(
                                                name,
                                                type_resolve(
                                                        ty,
                                                        v__(e->left->es, i)
                                                ),
                                                true
                                        )
                                );
                        }
                } else {
                        avP(t0->params, PARAM(NULL, type_resolve(ty, e->left), true));
                }
                t0->rt = SeqToList(type_resolve(ty, e->right));
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
                return NIL_TYPE;

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

static bool
unify2_(Ty *ty, Type **t0, Type *t1, bool check)
{
        TLOG("unify2()");
        TLOG("    %s", ShowType(*t0));
        TLOG("    %s\n", ShowType(t1));

        if (IsUnknown(Resolve(ty, t1))) {
                *t0 = UNKNOWN;
                return true;
        }

        if (*t0 == NULL || IsAny(t1) || *t0 == NONE_TYPE) {
                *t0 = type_really_unfixed(ty, t1);
                return true;
        }

        if (IsUnknown(*t0)) {
                return true;
        }

        if (
                UnifyX(ty, *t0, t1, true, false)
             || UnifyX(ty, t1, *t0, false, false)
        ) {
                return true;
        }

        if (
                ClassOfType(ty, t1) == CLASS_INT
             && CollapseInts(ty, t0)
        ) {
                return true;
        }

        if (
                IsTagged(*t0)
             && IsTagged(t1)
             && (*t0)->class == t1->class
        ) {
                unify2_(ty, v_((*t0)->args, 0), v__(t1->args, 0), check);
        } else if (t1->type == TYPE_UNION) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        unify2_(ty, t0, v__(t1->types, i), check);
                }
        } else if ((*t0)->type == TYPE_UNION && !(*t0)->fixed) {
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        if (try_coalesce(ty, v_((*t0)->types, i), t1)) {
                                return true;
                        }
                }
                avP((*t0)->types, t1);
                *t0 = Reduce(ty, *t0);
        } else if (!IsFixed(*t0)) {
                Type *union_ = NewType(ty, TYPE_UNION);
                avP(union_->types, *t0);
                avP(union_->types, t1);
                *t0 = Reduce(ty, union_);
        }

        return UnifyX(ty, *t0, t1, true, true);
}

void
unify2(Ty *ty, Type **t0, Type *t1)
{
        unify2_(ty, t0, t1, true);
}

void
unify(Ty *ty, Type **t0, Type *t1)
{
        if (*t0 == NULL) {
                *t0 = NewVar(ty);
        }

        UnifyX(ty, *t0, t1, true, true);
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
type_show(Ty *ty, Type const *t0)
{
        static TypeVector visiting;
        byte_vector buf = {0};

        t0 = ResolveVar(t0);

        if (t0 == NULL) {
                return sclone_malloc("⭕️");
        }

        if (IsUnknown(t0)) {
                return sclone_malloc("🟢");
        }

        if (IsBottom(t0)) {
                return sclone_malloc("🔴");
        }

        if (already_visiting(&visiting, t0) || vN(visiting) > 24) {
                return sclone_malloc("...");
        } else {
                xvP(visiting, (Type *)t0);
        }

        if (IsFixed(t0)) {
                //dump(&buf, "!");
        }

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                if (t0->concrete) {
                        dump(&buf, "%s", TERM(92;1));
                }
                switch (t0->class->i) {
                case CLASS_TOP:     dump(&buf, "%sAny%s", TERM(93), TERM(0));    break;
                case CLASS_INT:     dump(&buf, "%sInt%s", TERM(93), TERM(0));    break;
                case CLASS_FLOAT:   dump(&buf, "%sFloat%s", TERM(93), TERM(0));  break;
                case CLASS_STRING:  dump(&buf, "%sString%s", TERM(93), TERM(0)); break;
                case CLASS_BOOL:    dump(&buf, "%sBool%s", TERM(93), TERM(0));   break;
                case CLASS_BLOB:    dump(&buf, "%sBlob%s", TERM(93), TERM(0));   break;
                case CLASS_ARRAY:   dump(&buf, "%sArray%s", TERM(93), TERM(0));  break;
                case CLASS_DICT:    dump(&buf, "%sDict%s", TERM(93), TERM(0));   break;
                case CLASS_NIL:     dump(&buf, "%snil%s", TERM(93), TERM(0));    break;
                default:            dump(&buf, "%s",  t0->class->name); break;
                }
                dump(&buf, "%s", TERM(0));
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
                //dump(&buf, "%sunion[%s", TERM(96), TERM(0));
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (i > 0) {
                                dump(
                                        &buf,
                                        " %s|%s ",
                                        TERM(38;2;33;155;255),
                                        TERM(0)
                                );
                        }
                        dump(&buf, "%s", ShowType(v__(t0->types, i)));
                }
                //dump(&buf, "%s]%s", TERM(96), TERM(0));
                break;
        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        Type *t1 = v__(t0->types, i);
                        if (i > 0) {
                                dump(
                                        &buf,
                                        " %s&%s ",
                                        TERM(38;2;245;115;64),
                                        TERM(0)
                                );
                        }
                        if (t1 != NULL && t1->type == TYPE_UNION) {
                                dump(&buf, "(%s)", ShowType(v__(t0->types, i)));
                        } else {
                                dump(&buf, "%s", ShowType(v__(t0->types, i)));
                        }
                }
                break;
        case TYPE_FUNCTION:
                if (vN(t0->bound) > 0) {
                        dump(&buf, "%s[", TERM(38;2;255;153;187));
                        for (int i = 0; i < vN(t0->bound); ++i) {
                                if (i > 0) {
                                        dump(&buf, ", ");
                                }
                                dump(&buf, "%s", VarName(ty, v__(t0->bound, i)), TERM(0));
                        }
                        dump(&buf, "]%s", TERM(0));
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
                dump(&buf, "%s(%s", TERM(1;38;2;178;153;191), TERM(0));
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
                        char const *pre = p->rest ? "..."
                                        : p->kws ? "%"
                                        : p->required ? "?"
                                        : "";
                        if (p->name == NULL) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s%s%s%s" : ", %s%s%s%s",
                                        TERM(93;1),
                                        pre,
                                        TERM(0),
                                        ShowType(p->type)
                                );
                        } else {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s%s%s: %s%s%s%s" : ", %s%s%s: %s%s%s%s",
                                        TERM(38;2;178;153;191),
                                        p->name,
                                        TERM(0),
                                        TERM(93;1),
                                        pre,
                                        TERM(0),
                                        ShowType(p->type)
                                );
                        }

                }
                if (vN(t0->params) != 1 || v_(t0->params, 0)->name != NULL) {
                        dump(
                                &buf,
                                "%s) ->%s %s",
                                TERM(1;38;2;178;153;191),
                                TERM(0),
                                ShowType(t0->rt)
                        );
                } else {
                        dump(
                                &buf,
                                " %s->%s %s%s)%s",
                                TERM(1;38;2;178;153;191),
                                TERM(0),
                                ShowType(t0->rt),
                                TERM(1;38;2;178;153;191),
                                TERM(0)
                        );
                }
                break;
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                dump(&buf, t0->type == TYPE_LIST ? "list" : "seq");
        case TYPE_TUPLE:
                if (is_record(t0)) {
                        dump(&buf, "%s{%s", TERM(38;2;240;158;58), TERM(0));
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
                                                (i == 0) ? "%s%s:%s %s" : ", %s%s%s: %s",
                                                TERM(38;2;240;158;58),
                                                v__(t0->names, i),
                                                TERM(0),
                                                ShowType(v__(t0->types, i))
                                        );
                                }
                        }
                        dump(&buf, "%s}%s", TERM(38;2;240;158;58), TERM(0));
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
                dump(&buf, "%s", IsTVar(t0) ? TERM(38;2;255;153;187) : TERM(91;1));
                if (t0->variadic) {
                        dump(&buf, "*");
                }
                dump(&buf, "%s%s", CanBind(t0) ? "$" : "", VarName(ty, t0->id));
                dump(&buf, "%s", TERM(0));
                if (IsBoundVar(t0)) {
                        dump(
                                &buf,
                                "%s%s%s(%s)",
                                t0->fixed ? TERM(91) : TERM(92),
                                t0->fixed ? "==" : "=",
                                TERM(0),
                                ShowType(t0->val)
                        );
                } else if (!IsTVar(t0)) {
                        //dump(&buf, "%s{%d}%s", (t0->level >= CurrentLevel) ? TERM(94) : TERM(96), t0->level, TERM(0));
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

        case TYPE_SUBSCRIPT:
                dump(&buf, "%s[%d]", ShowType(t0->val), t0->i);
                break;

        case TYPE_SLICE:
                dump(&buf, "%s", ShowType(t0->val));
                dump(&buf, "[");
                if (t0->i != 0) {
                        dump(&buf, "%d", t0->i);
                }
                dump(&buf, ":");
                if (t0->j != INT_MAX) {
                        dump(&buf, "%d", t0->j);
                }
                if (t0->k != 1) {
                        dump(&buf, ":%d", t0->k);
                }
                dump(&buf, "]");
                break;

        case TYPE_ALIAS:
                if (vN(t0->args) > 0) {
                        dump(&buf, "%s%s[%s", TERM(38;2;150;199;97), t0->name, TERM(0));
                        for (int i = 0; i < vN(t0->args); ++i) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        ShowType(v__(t0->args, i))
                                );
                        }
                        dump(&buf, "%s]%s", TERM(38;2;150;199;97), TERM(0));
                } else {
                        dump(&buf, "%s%s%s", TERM(38;2;150;199;97), t0->name, TERM(0));
                }
                break;

        case TYPE_NIL:
                dump(&buf, "%snil%s", TERM(94), TERM(0));
                break;

        case TYPE_NONE:
                dump(&buf, "<none>");
                break;

        case TYPE_INTEGER:
                dump(&buf, "%s%"PRIiMAX"%s", TERM(94), t0->z, TERM(0));
                break;

        case TYPE_ERROR:
                dump(&buf, "❌");
                break;

        case TYPE_COMPUTED:
                if (t0->val != NULL) {
                        dump(&buf, "%s", ShowType(t0->val));
                } else {
                        dump(&buf, "%s%s(%s", TERM(92), name_of(&t0->func), TERM(0));
                        for (int i = 0; i < vN(t0->args); ++i) {
                                if (i > 0) {
                                        dump(&buf, ", ");
                                }
                                dump(&buf, ShowType(v__(t0->args, i)));
                        }
                        dump(&buf, "%s)%s", TERM(92), TERM(0));
                }
                break;
        }

        vvX(visiting);

        return vN(buf) == 0 ? sclone_malloc("<?>") : buf.items;
}

Type *
type_unfixed(Ty *ty, Type *t0)
{
        Type *t;

        if (IsBottom(t0)) {
                return BOTTOM;
        }

        if (t0->fixed) {
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
        return type_unfixed(ty, t0);
        return PropagateX(ty, t0, false, PROP_UNFIX);
}

static bool
IsSolved(Type const *t0)
{
        while (IsBoundVar(t0)) {
                if (!t0->bounded) {
                        return false;
                }
                t0 = t0->val;
        }

        switch (TypeType(t0)) {
        case TYPE_VARIABLE:
                return IsTVar(t0);

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                return IsSolved(t0->val);

        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_TUPLE:
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!IsSolved(v__(t0->types, i))) {
                                return false;
                        }
                }
                break;

        case TYPE_ALIAS:
        case TYPE_OBJECT:
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (!IsSolved(v__(t0->args, i))) {
                                return false;
                        }
                }
                break;

        case TYPE_FUNCTION:
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
                        if (!IsSolved(p->type)) {
                                return false;
                        }
                }
                if (!IsSolved(t0->rt)) {
                        return false;
                }
                break;

        case TYPE_COMPUTED:
                return t0->inst && (t0->val == NULL);
        }

        return true;
}

static Type *
MakeConcrete_(Ty *ty, Type *t0, TypeVector *refs, bool variance)
{
        static TypeVector visiting;

        while (IsBoundVar(t0)) {
                if (!t0->bounded) {
                        return variance ? TYPE_ANY : UNKNOWN;
                }
                t0 = t0->val;
        }

        if (IsBottom(t0)) {
                return UNKNOWN;
        }

        if (t0->concrete) {
                //return t0;
        }

        if (CanBind(t0)) {
                if (t0->level <= CurrentLevel) {
                        return t0;
                } else {
                        Type *t1 = LookEnv(ty, ty->tenv, t0->id);
                        Type *t2 = (t1 == NULL || t1 == NONE_TYPE)
                                 ? (variance ? ANY : UNKNOWN)
                                 : t1;
                        XXTLOG("MakeConcrete(): %s -> %s", ShowType(t0), ShowType(t2));
                        return t2;
                }
        }

        if (already_visiting(&visiting, t0)) {
                return UNKNOWN;
        } else {
                xvP(visiting, t0);
        }


        t0 = CloneType(ty, t0);
        t0->concrete = true;
        t0->fixed = true;

        switch (t0->type) {
        case TYPE_VARIABLE:
                break;

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                t0 = CanStep(t0)
                   ? MakeConcrete_(ty, StepVar(t0), refs, variance)
                   : true ? t0 : (variance ? TYPE_ANY : UNKNOWN);
                break;

        case TYPE_UNION:
                CloneVec(t0->types);
                for (int i = 0; i < vN(t0->types); ++i) {
                        *v_(t0->types, i) = MakeConcrete_(ty, v__(t0->types, i), refs, variance);
                        if (IsAny(v__(t0->types, i))) {
                                t0 = ANY;
                                break;
                        }
                }
                t0 = Reduce(ty, t0);
                break;

        case TYPE_INTERSECT:
                CloneVec(t0->types);
                for (int i = 0; i < vN(t0->types); ++i) {
                        *v_(t0->types, i) = MakeConcrete_(ty, v__(t0->types, i), refs, variance);
                        if (IsBottom(v__(t0->types, i))) {
                                t0 = UNKNOWN;
                                break;
                        }
                }
                break;

        case TYPE_TUPLE:
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                CloneVec(t0->types);
                for (int i = 0; i < vN(t0->types); ++i) {
                        *v_(t0->types, i) = MakeConcrete_(ty, v__(t0->types, i), refs, variance);
                }
                break;

        case TYPE_ALIAS:
                if (refs != NULL && t0->_type == NULL) {
                        xvP(*refs, t0);
                }
        case TYPE_OBJECT:
                CloneVec(t0->args);
                for (int i = 0; i < vN(t0->args); ++i) {
                        *v_(t0->args, i) = MakeConcrete_(ty, v__(t0->args, i), refs, variance);
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_FUNCTION:
                CloneVec(t0->params);
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param *p = v_(t0->params, i);
                        p->type = MakeConcrete_(ty, p->type, refs, !variance);
                }
                t0->rt = MakeConcrete_(ty, t0->rt, refs, variance);
                break;

        case TYPE_INTEGER:
                t0->type = TYPE_OBJECT;
                t0->class = TYPE_INT->class;
                v00(t0->args);
                v00(t0->bound);
                break;
        }

        vvX(visiting);

        return t0;
}

static Type *
MakeConcrete(Ty *ty, Type *t0, TypeVector *refs)
{
        return MakeConcrete_(ty, t0, refs, false);
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

        if (IsBottom(t0) || IsBottom(t1)) {
                return BOTTOM;
        }

        if (t0->type == TYPE_UNION) {
                Type *t = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify2(
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

        if (t1->type == TYPE_UNION) {
                Type *t = NULL;
                for (int i = 0; i < vN(t1->types); ++i) {
                        unify2(
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

        int c0 = ClassOfType(ty, t0);
        int c1 = ClassOfType(ty, t1);

        if (c0 < 0 || c1 < 0) {
                return NULL;
        }

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

                case OP_IN:
                case OP_NOT_IN:
                        return TYPE_BOOL;
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
        case EXPRESSION_PLUS:    op = OP_ADD;    break;
        case EXPRESSION_MINUS:   op = OP_SUB;    break;
        case EXPRESSION_DIV:     op = OP_DIV;    break;
        case EXPRESSION_STAR:    op = OP_MUL;    break;
        case EXPRESSION_PERCENT: op = OP_MOD;    break;
        case EXPRESSION_IN:      op = OP_IN;     break;
        case EXPRESSION_NOT_IN:  op = OP_NOT_IN; break;
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
type_unary_hash_t(Ty *ty, Type const *t0)
{
        Type *t1 = NULL;

        Type const *t00 = t0;
        t0 = Resolve(ty, t0);

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
        case TYPE_CLASS:
                if (IsTagged(t0)) {
                        t1 = TypeArg(t0, 0);
                        break;
                }
                switch (StrictClassOf(t0)) {
                case CLASS_ARRAY:
                case CLASS_DICT:
                case CLASS_STRING:
                case CLASS_BLOB:
                        t1 = TYPE_INT;
                        break;
                }
                if (t1 == NULL) {
                        type_method_call_name(ty, (Type *)t0, M_NAME(NAMES._len_));
                }
                break;

        case TYPE_TUPLE:
                t1 = TYPE_INT;
                break;

        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        unify2(
                                ty,
                                &t1,
                                type_unary_hash_t(ty, v__(t0->types, i))
                        );
                }
                break;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        type_intersect(
                                ty,
                                &t1,
                                type_unary_hash_t(ty, v__(t0->types, i))
                        );
                }
                break;

        case TYPE_BOTTOM:
                t1 = BOTTOM;
                break;
        }

        XXTLOG("Count():");
        XXTLOG("   #%s", ShowType(t00));
        XXTLOG(" -> %s", ShowType(t1));

        return t1;
}

Type *
type_unary_op(Ty *ty, Expr const *e)
{
        Type *t0 = e->_type;
        return NULL;
}

Type *
type_wtf(Ty *ty, Expr const *e)
{
        Type *t0 = NewVar(ty);

        Unify(ty, Either(ty, t0, NIL_TYPE), e->left->_type, true);
        Unify(ty, t0, e->right->_type, true);

        return t0;
}

Type *
type_array_of(Ty *ty, Type *t0)
{
        Type *t1 = ArrayOf(ty, t0);
        ApplyConstraints(ty);
        return Generalize(ty, t1);
}

Type *
type_dict_of(Ty *ty, Type *t0, Type *t1)
{
        Type *t2 = DictOf(ty, t0, t1);
        ApplyConstraints(ty);
        return Generalize(ty, t2);
}

Type *
type_either(Ty *ty, Type *t0, Type *t1)
{
        return (t0 == NULL) ? t1 : Either(ty, t0, t1);
}

Type *
type_both(Ty *ty, Type *t0, Type *t1)
{
        if (IsBottom(t0)) {
                return t1;
        }

        if (t0->type == TYPE_INTERSECT) {
                avP(t0->types, t1);
        } else {
                Type *t2 = NewType(ty, TYPE_INTERSECT);
                avP(t2->types, t0);
                avP(t2->types, t1);
                t0 = t2;
        }

        return Reduce(ty, t0);
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
                Unify(ty, t0, t2, true);
                //return Generalize(ty, t1);
                return t1;
        }

        Class *c;
        ClassDefinition *def;

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                switch (ClassOfType(ty, t0)) {
                case CLASS_ARRAY:
                        t1 = NewType(ty, TYPE_LIST);
                        avP(t1->types, TypeArg(t0, 0));
                        avP(t1->types, TYPE_INT);
                        break;
                case CLASS_STRING:
                        t1 = NewType(ty, TYPE_LIST);
                        avP(t1->types, TYPE_STRING);
                        avP(t1->types, TYPE_INT);
                        break;
                case CLASS_DICT:
                        t1 = NewType(ty, TYPE_LIST);
                        avP(t1->types, TypeArg(t0, 0));
                        avP(t1->types, TypeArg(t0, 1));
                        avP(t1->types, TYPE_INT);
                        break;
                case CLASS_ITERABLE:
                case CLASS_ITER:
                        t1 = TypeArg(t0, 0);
                        break;
                }
                if (t1 != NULL) {
                        break;
                }
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

Type *
type_not_nil(Ty *ty, Type *t0)
{
        Type *u0 = NewVar(ty);

        UnifyX(ty, Either(ty, u0, NIL_TYPE), t0, true, true);

        return u0;
}

static Type *
BoundedBy(Ty *ty, Type *t0, Type *t1)
{
        Type *t2;
        Type *t3;

        if (type_check(ty, t1, t0)) {
                t2 = t0;
                goto End;
        }

        t0 = Resolve(ty, t0);
        t1 = Resolve(ty, t1);

        switch (TypeType(t0)) {
        case TYPE_UNION:
                t2 = NULL;
                for (int i = 0; i < vN(t0->types); ++i) {
                        t3 = BoundedBy(ty, v__(t0->types, i), t1);
                        if (!IsBottom(t3)) {
                                unify2(ty, &t2, t3);
                        }
                }
                break;

        default:
                t2 = NULL;
        }

End:
        XXTLOG("BoundedBy():");
        XXTLOG("    %s", ShowType(t0));
        XXTLOG("  < %s", ShowType(t1));
        XXTLOG("  = %s", ShowType(t2));

        return t2;
}

Type *
type_instance_of(Ty *ty, Type *t0, int class)
{
        Type *t1 = NewType(ty, TYPE_OBJECT);
        t1->class = class_get_class(ty, class);
        avP(t1->args, ANY);

        Type *t2 = BoundedBy(ty, t0, t1);

        return (t2 != NULL) ? t2 : t1;
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

static void
fixup(Ty *ty, Type *t0)
{
        Type *g0 = Generalize(ty, t0);
        TLOG("  g0:  %s", ShowType(g0));

        TypeEnv *env = ty->tenv;
        ty->tenv = NewEnv(ty, env);

        int nparam = vN(g0->bound);
        for (int i = 0; i < nparam; ++i) {
                u32 id = v__(g0->bound, i);
                int nref = 0;
                for (int i = 0; i < vN(g0->params); ++i) {
                        Param const *p = v_(g0->params, i);
                        if (RefersTo(p->type, id)) {
                                nref += 1;
                        }
                }
                if (RefersTo(g0->rt, id)) {
                        nref += 1;
                }
                if (nref > 0) {
                        Type *var0 = NewTVar(ty);
                        PutEnv(ty, ty->tenv, id, var0);
                        avP(g0->bound, var0->id);
                }
        }

        g0 = MakeConcrete(ty, g0, NULL);
        TLOG("  g0:  %s", ShowType(g0));

        *t0 = *Reduce(ty, Generalize(ty, g0));
        XXTLOG("  t0:  %s", ShowType(t0));

        ty->tenv = env;

        if (FUEL > 0) {
                FUEL = MAX_FUEL;
        }
}

void
type_function_fixup(Ty *ty, Expr const *e)
{
        Type *t0 = e->_type;

        if (TypeType(t0) != TYPE_FUNCTION) {
                return;
        }

        ApplyConstraints(ty);

        for (int i = 0; i < vN(t0->params); ++i) {
                Expr *dflt = v__(e->dflts, i);
                if (dflt != NULL && dflt->_type != NULL) {
                        //type_check(ty, psym->type, dflt->_type);
                        //unify2(ty, &psym->type, dflt->_type);
                }
        }

        fixup(ty, t0);

        if (e->class > -1) {
                XXTLOG("fixup(%s.%s)[%d]:", class_name(ty, e->class), e->name, CurrentLevel);
                XXTLOG("    %s", ShowType(t0));
        } else {
                XXTLOG("fixup()[%d]:", CurrentLevel);
                XXTLOG("    %s", ShowType(t0));
        }
}

Type **
FindRecordEntry(Type const *t0, int i, char const *name)
{
        if (TypeType(t0) != TYPE_TUPLE) {
                return NULL;
        }

        if (name == NULL) {
                return (i < vN(t0->types)) ? v_(t0->types, i) : NULL;
        }

        for (int i = 0; i < vN(t0->types); ++i) {
                if (
                        v__(t0->names, i) != NULL
                     && strcmp(v__(t0->names, i), name) == 0
                ) {
                        return v_(t0->types, i);
                }
        }

        return NULL;
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

        if (t1 == NULL || (*t0)->fixed || type_check(ty, *t0, t1)) {
                return;
        }

        if (UnifyX(ty, *t0, t1, false, false)) {
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

        if (t1->type == TYPE_INTERSECT) {
                for (int i = 0; i < vN(t1->types); ++i) {
                        type_intersect(ty, t0, v__(t1->types, i));
                }
                return;
        }

        if (
                TypeType(*t0) == TYPE_TUPLE
             && TypeType(t1) == TYPE_TUPLE
        ) {
                *t0 = CloneType(ty, *t0);
                CloneVec((*t0)->types);
                CloneVec((*t0)->names);

                for (int i = 0; i < vN(t1->types); ++i) {
                        char const *name = v__(t1->names, i);
                        Type *e1 = v__(t1->types, i);
                        Type **e2 = FindRecordEntry(*t0, i, name);
                        if (e2 == NULL) {
                                avP((*t0)->types, e1);
                                avP((*t0)->names, name);
                        } else {
                                type_intersect(ty, e2, e1);
                        }
                }

                return;
        }

        return;

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

        if (!type_check(ty, *t0, t1)) {
                return;
        }

        Type *t = *t0;

        switch ((*t0)->type) {
        case TYPE_UNION:
                t = CloneType(ty, *t0);
                v00(t->types);
                for (int i = 0; i < vN((*t0)->types); ++i) {
                        Type *t2 = v__((*t0)->types, i);
                        if (!type_check(ty, t1, t2)) {
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

        case TYPE_VARIABLE:
                t = *t0;
                type_subtract(ty, &(*t0)->val, t1);
                break;
        }

        XXTLOG("subtract():");
        XXTLOG("    %s", ShowType(*t0));
        XXTLOG("  - %s", ShowType(t1));
        XXTLOG("  = %s", ShowType(t));

        *t0 = t;
}

bool
TypeCheck(Ty *ty, Type *t0, Value const *v)
{
        XXTLOG("TypeCheck():");
        XXTLOG("    %s", VSC(v));
        XXTLOG("    %s", ShowType(t0));

        t0 = Resolve(ty, t0);

        if (IsBottom(t0)) {
                return true;
        }

        if (v->type == VALUE_NIL) {
                return type_check_x(ty, t0, NIL_TYPE, false);
        }

        switch (t0->type) {
        case TYPE_INTEGER:
                return v->type == VALUE_INTEGER
                    && v->integer == t0->z;

        case TYPE_VARIABLE:
        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
        case TYPE_SEQUENCE:
        case TYPE_LIST:
        case TYPE_COMPUTED:
                return true;

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
                                Value const *item = (name != NULL) ? tuple_get(v, name)
                                                  : (v->count > i) ? &v->items[i]
                                                  : /*)  else  (*/   NULL;
                                if (
                                        !TypeCheck(
                                                ty,
                                                v__(t0->types, i),
                                                (item != NULL) ? item : &STATIC_NIL
                                        )
                                ) {
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
                        if (
                                !class_is_subclass(ty, ClassOf(v), t0->class->i)
                        ) {
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

void
type_completions(Ty *ty, Type const *t0, char const *pre, ValueVector *out)
{
        expression_vector exprs = {0};

        int prefix_len = (pre == NULL) ? 0 : strlen(pre);

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                class_completions(ty, StrictClassOf(t0), pre, &exprs);
                for (int i = 0; i < vN(exprs); ++i) {
                        Expr const *e = v__(exprs, i);
                        switch (e->type) {
                        case EXPRESSION_FUNCTION:
                                xvP(
                                        *out,
                                        vTn(
                                                "name", xSz(e->name),
                                                "doc",  (e->doc == NULL) ? NIL : xSz(e->doc),
                                                "type", xSz(ShowType(SolveMemberAccess(ty, (Type *)t0, e->_type))),
                                                "kind", (e->mtype == MT_GET) ? INTEGER(10) : INTEGER(2)
                                        )
                                );
                                break;
                        case EXPRESSION_IDENTIFIER:
                                xvP(
                                        *out,
                                        vTn(
                                                "name",  xSz(e->identifier),
                                                "doc",   (e->doc == NULL) ? NIL : xSz(e->doc),
                                                "type",  xSz(ShowType(SolveMemberAccess(ty, (Type *)t0, e->_type))),
                                                "kind",  INTEGER(5)
                                        )
                                );
                                break;
                        case EXPRESSION_EQ:
                                xvP(
                                        *out,
                                        vTn(
                                                "name",  xSz(e->target->identifier),
                                                "doc",   (e->doc == NULL) ? NIL : xSz(e->doc),
                                                "type",  xSz(ShowType(SolveMemberAccess(ty, (Type *)t0, e->target->_type))),
                                                "kind",  INTEGER(5)
                                        )
                                );
                                break;
                        }
                }

        case TYPE_TUPLE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        char num[32];
                        char const *name = v__(t0->names, i);
                        if (name == NULL) {
                                snprintf(num, sizeof num, "%d", i);
                                name = num;
                        }
                        if (strncmp(name, pre, prefix_len) != 0) {
                                continue;
                        }
                        xvP(
                                *out,
                                vTn(
                                        "name", vSsz(name),
                                        "doc",  NIL,
                                        "type", xSz(ShowType(v__(t0->types, i))),
                                        "kind", INTEGER(5)
                                )
                        );
                }
                break;

        case TYPE_INTERSECT:
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        type_completions(ty, v__(t0->types, i), pre, out);
                }
                break;

        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        type_completions(ty, t0->val, pre, out);
                }
                break;

        case TYPE_ALIAS:
                type_completions(ty, ResolveAlias(ty, t0), pre, out);
                break;
        }
}

bool
type_find_method(Ty *ty, Type const *t0, char const *name, Type **t1, Expr **e)
{
        *t1 = NULL;
        *e = NULL;

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                *e = FindMethod(t0->class, name);
                if (*e != NULL) {
                        *t1 = (*e)->_type;
                }
                break;
        case TYPE_CLASS:
                *e = FindStatic(t0->class, name);
                if (*e != NULL) {
                        *t1 = (*e)->_type;
                }
                break;
        case TYPE_TUPLE:
                *t1 = type_member_access_t(ty, t0, name, false);
                break;
        case TYPE_INTERSECT:
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (type_find_method(ty, v__(t0->types, i), name, t1, e)) {
                                break;
                        }
                }
                break;
        }

        return *t1 != NULL;
}

bool
type_is_concrete(Ty *ty, Type const *t0)
{
        return !Occurs(ty, (Type *)t0, 0, -1);
}

bool
type_is_tvar(Type const *t0)
{
        return IsTVar(t0);
}

static TypeVector
TyTypeVector(Ty *ty, Value const *v)
{
        TypeVector types = {0};

        switch (v->type) {
        case VALUE_ARRAY:
                for (int i = 0; i < vN(*v->array); ++i) {
                        avP(types, type_from_ty(ty, v_(*v->array, i)));
                }
                break;

        case VALUE_TUPLE:
                for (int i = 0; i < v->count; ++i) {
                        avP(types, type_from_ty(ty, &v->items[i]));
                }
                break;

        case VALUE_NIL:
                break;

        default:
                CompileError(ty, "expected type vector but got: %s", VSC(v));
                UNREACHABLE();
        }

        return types;
}

static Class *
TyTypeClass(Ty *ty, Value const *v)
{
        if (v->type == VALUE_CLASS) {
                return class_get_class(ty, v->class);
        } else if (
                v->type == VALUE_TYPE
             && v->ptr != NULL
             && ((Type *)v->ptr)->type == TYPE_CLASS
        ) {
                return ((Type *)v->ptr)->class;
        } else {
                CompileError(ty, "expected class but got: %s", VSC(v));
                UNREACHABLE();
        }
}

Type *
type_from_ty(Ty *ty, Value const *v)
{
        Type *t0 = NULL;

        if (v->type == VALUE_NIL) {
                return NIL_TYPE;
        }

        if (v->type == VALUE_TAG) switch (v->tag) {
        case TyNilT:
                return NIL_TYPE;

        case TyBottomT:
                return BOTTOM;

        case TyUnknownT:
                return UNKNOWN;

        case TyAnyT:
                return ANY;

        case TyIntT:
                return TYPE_INT;

        case TyStringT:
                return TYPE_STRING;

        case TyRegexT:
                return TYPE_REGEX;

        case TyFloatT:
                return TYPE_FLOAT;

        case TyBoolT:
                return TYPE_BOOL;

        case TyArrayT:
                return TYPE_ARRAY;

        case TyDictT:
                return TYPE_DICT;

        case TyErrorT:
                return &ERROR;

        case TyObjectT:
                return NewObject(CLASS_OBJECT);
        }

        if (v->type == VALUE_CLASS) {
                return class_get_class(ty, v->class)->object_type;
        }

        Value inner = unwrap(ty, v);

        if (v->type == VALUE_TUPLE) {
                goto RecordType;
        }

        int tag = tags_first(ty, v->tags);
        if (tag == -1) {
                return UNKNOWN;
        }

        switch (tag) {
        case TyUnionT:
                t0 = NewType(ty, TYPE_UNION);
                t0->types = TyTypeVector(ty, &inner);
                break;

        case TyIntersectT:
                t0 = NewType(ty, TYPE_INTERSECT);
                t0->types = TyTypeVector(ty, &inner);
                break;

        case TyObjectT:
                t0 = NewType(ty, TYPE_OBJECT);
                if (
                        (inner.type == VALUE_TUPLE)
                     && (inner.count == 2)
                     && (inner.items[1].type == VALUE_ARRAY)
                ) {
                        t0->class = TyTypeClass(ty, &inner.items[0]);
                        t0->args = TyTypeVector(ty, &inner.items[1]);
                } else if (
                        (inner.type == VALUE_TUPLE)
                     && (inner.count >= 2)
                ) {
                        t0->class = TyTypeClass(ty, &inner.items[0]);
                        t0->args = TyTypeVector(ty, &TUPLE(&inner.items[1], NULL, inner.count - 1, false));
                } else {
                        t0->class = TyTypeClass(ty, &inner);
                }
                break;

        case TyClassT:
                t0 = NewType(ty, TYPE_CLASS);
                t0->class = TyTypeClass(ty, &inner);
                break;

        case TyListT:
                t0 = NewType(ty, TYPE_INTERSECT);
                t0->types = TyTypeVector(ty, &inner);
                break;

        case TyHoleT:
                if (inner.type != VALUE_TYPE) {
                        CompileError(ty, "expected type hole but got: %s", VSC(v));
                        UNREACHABLE();
                }
                t0 = inner.ptr;
                break;

        case TyVarT:
                if (inner.type != VALUE_INTEGER) {
                        CompileError(ty, "expected type variable ID but got: %s", VSC(&inner));
                }
                t0 = NewType(ty, TYPE_VARIABLE);
                t0->id = inner.integer;
                t0->level = 0;
                t0->val = TVAR;
                break;

        case TyRecordT:
RecordType:
                t0 = NewType(ty, TYPE_TUPLE);
                for (int i = 0; i < inner.count; ++i) {
                        avP(t0->types, type_from_ty(ty, &inner.items[i]));
                        if (inner.ids[i] == -1) {
                                avP(t0->names, NULL);
                        } else {
                                avP(t0->names, M_NAME(inner.ids[i]));
                        }
                }
                break;

        case TyFuncT:
                t0 = NewType(ty, TYPE_FUNCTION);
                if (inner.type != VALUE_TUPLE || inner.count != 3) {
                        CompileError(ty, "expected (TVars, Params, ReturnType) tuple but got: %s", VSC(&inner));
                        UNREACHABLE();
                }
                if (inner.items[0].type != VALUE_ARRAY) {
                        goto Fail;
                }
                for (int i = 0; i < vN(*inner.items[0].array); ++i) {
                        Value const *id = v_(*inner.items[0].array, i);
                        if (id->type == VALUE_INTEGER) {
                                avP(t0->bound, id->integer);
                        } else if (id->type == VALUE_TYPE && IsTVar(id->ptr)) {
                                avP(t0->bound, ((Type *)id->ptr)->id);
                        } else {
                                goto Fail;
                        }
                }
                if (inner.items[1].type != VALUE_ARRAY) {
                        goto Fail;
                }
                for (int i = 0; i < vN(*inner.items[1].array); ++i) {
                        Value const *name = tget_t(v_(*inner.items[1].array, i), "name", VALUE_STRING);
                        Value const type = tget_or(v_(*inner.items[1].array, i), "type", TYPE(UNKNOWN));
                        Value const req = tget_or(v_(*inner.items[1].array, i), "required", BOOLEAN(false));
                        avP(t0->params, PARAM(mkcstr(ty, name), type_from_ty(ty, &type), value_truthy(ty, &req)));
                }
                t0->rt = type_from_ty(ty, &inner.items[2]);
                break;
        }

        if (t0 == NULL) {
Fail:
                CompileError(ty, "invalid type spec: %s", v);
        }

        return t0;
}

Value
type_to_ty(Ty *ty, Type *t0)
{
        Value v = NIL;
        Array *types;
        Array *params;
        Array *bound;
        Param const *param;

        t0 = ResolveVar(t0);

        if (IsAny(t0)) {
                return TAG(TyAnyT);
        }

        switch (TypeType(t0)) {
        case TYPE_BOTTOM:
                v = TAG(IsUnknown(t0) ? TyUnknownT : TyBottomT);
                break;

        case TYPE_NIL:
                v = TAG(TyNilT);
                break;

        case TYPE_VARIABLE:
                if (IsTVar(t0)) {
                        v = tagged(ty, TyVarT, INTEGER(t0->id), NONE);
                } else {
                        v = tagged(ty, TyHoleT, TYPE(t0), NONE);
                }
                break;

        case TYPE_TUPLE:
                v = is_record(t0) ? value_record(ty, vN(t0->types)) : vT(vN(t0->types));
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (v__(t0->names, i) != NULL) {
                                v.ids[i] = M_ID(v__(t0->names, i));
                        }
                        v.items[i] = type_to_ty(ty, v__(t0->types, i));
                }
                break;

        case TYPE_OBJECT:
                types = vAn(vN(t0->args));
                for (int i = 0; i < vN(t0->args); ++i) {
                        vPx(*types, type_to_ty(ty, v__(t0->args, i)));
                }
                v = tagged(ty, TyObjectT, CLASS(t0->class->i), ARRAY(types), NONE);
                break;

        case TYPE_UNION:
                types = vAn(vN(t0->types));
                for (int i = 0; i < vN(t0->types); ++i) {
                        vPx(*types, type_to_ty(ty, v__(t0->types, i)));
                }
                v = tagged(ty, TyUnionT, ARRAY(types), NONE);
                break;

        case TYPE_INTERSECT:
                types = vAn(vN(t0->types));
                for (int i = 0; i < vN(t0->types); ++i) {
                        vPx(*types, type_to_ty(ty, v__(t0->types, i)));
                }
                v = tagged(ty, TyIntersectT, ARRAY(types), NONE);
                break;

        case TYPE_LIST:
                types = vAn(vN(t0->types));
                for (int i = 0; i < vN(t0->types); ++i) {
                        vPx(*types, type_to_ty(ty, v__(t0->types, i)));
                }
                v = tagged(ty, TyListT, ARRAY(types), NONE);
                break;

        case TYPE_FUNCTION:
                params = vAn(vN(t0->params));
                bound = vAn(vN(t0->bound));
                for (int i = 0; i < vN(t0->bound); ++i) {
                        vPx(*bound, tagged(ty, TyVarT, INTEGER(v__(t0->bound, i)), NONE));
                }
                for (int i = 0; i < vN(t0->params); ++i) {
                        param = v_(t0->params, i);
                        vPx(
                                *params,
                                vTn(
                                        "name",   vSsz(param->name),
                                        "type",   type_to_ty(ty, param->type),
                                        "gather", BOOLEAN(param->rest),
                                        "kwargs", BOOLEAN(param->kws)
                                )
                        );
                }
                v = tagged(
                        ty,
                        TyFuncT,
                        ARRAY(bound),
                        ARRAY(params),
                        type_to_ty(ty, t0->rt),
                        NONE
                );
                break;
        }

        return v;
}

/* vim: set sts=8 sw=8 expandtab: */
