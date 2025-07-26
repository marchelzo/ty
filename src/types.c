#include "scope.h"
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

#define TYPES_LOG 0

typedef struct {
        TypeVector id0;
        TypeVector id1;
        vec(bool) memo;
        vec(u64) times;
} TypeMemo;

u32 TYPES_OFF = 0;

#define ENFORCE (!AllowErrors && TYPES_OFF == 0 && !DEBUGGING)
#define ENABLED (CheckConstraints)

#define   xDDD() if (!ENABLED) { return NULL; }
#define  xDDDD() if (!ENABLED) { return true; }
#define xDDDDD() if (!ENABLED) { return;      }

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

#define NewObject(c, ...) ((NewObject)(ty,    c,  __VA_ARGS__ __VA_OPT__(,) NULL))
#define NewRecord(...)    ((NewRecord)(ty,        __VA_ARGS__ __VA_OPT__(,) NULL))
#define NewTuple(...)     ((NewTuple)(ty,         __VA_ARGS__ __VA_OPT__(,) NULL))
#define NewList(...)      ((NewList)(ty,          __VA_ARGS__ __VA_OPT__(,) NULL))
#define NewIntersect(...) ((NewIntersect)(ty,     __VA_ARGS__ __VA_OPT__(,) NULL))
#define NewUnion(...)     ((NewUnion)(ty,         __VA_ARGS__ __VA_OPT__(,) NULL))
#define NewFunction(...)  ((NewFunction)(ty,      __VA_ARGS__ __VA_OPT__(,) NULL))

#define NewDict(k, v) NewObject(CLASS_DICT,  (k), (v))
#define NewArray(t)   NewObject(CLASS_ARRAY, (t))

inline static void
TupleAddField(Ty *ty, Type *t0, Type *u0, char const *name, bool required)
{
        avP(t0->types, u0);
        avP(t0->names, name);
        avP(t0->required, required);
}

#define AddEntry_2(t, u)       TupleAddField(ty, (t), (u), NULL, true)
#define AddEntry_3(t, u, n)    TupleAddField(ty, (t), (u), (n),  true)
#define AddEntry_4(t, u, n, r) TupleAddField(ty, (t), (u), (n),  (r))
#define AddEntry(...) VA_SELECT(AddEntry, __VA_ARGS__)

inline static bool
IsRequired(Type const *t0, i32 i)
{
        switch (TypeType(t0)) {
        case TYPE_TUPLE:
                return v__(t0->required, i);

        case TYPE_FUNCTION:
                return v_(t0->params, i)->required;

        default:
                UNREACHABLE();
        }
}

#if TYPES_LOG
#define XXTLOG(fmt, ...) (EnableLogging > 0 && printf("[%2d] " fmt "\n", CurrentLevel __VA_OPT__(,) __VA_ARGS__))
#define XXXTLOG(fmt, ...) (printf("[%2d] " fmt "\n", CurrentLevel __VA_OPT__(,) __VA_ARGS__))
#define DPRINT(cond, fmt, ...) ((cond) && EnableLogging > 0 && printf("%*s" fmt "\n", 4*CurrentDepth, "" __VA_OPT__(,) __VA_ARGS__))
#define XDPRINT(cond, fmt, ...) ((cond) && printf("%*s" fmt "\n", 4*CurrentDepth, "" __VA_OPT__(,) __VA_ARGS__))
#else
#define XXTLOG(...) 0
#define XXXTLOG(...) 0
#define DPRINT(cond, fmt, ...) 0
#define XDPRINT(cond, fmt, ...) 0
#endif

#define TLOG(...)

static void *TVAR = (void *)&TVAR;
static void *HOLE = (void *)&HOLE;
static void *REPLACE = (void *)&REPLACE;
static void *NAMED = (void *)&NAMED;
static void *OPTIONAL = (void *)&OPTIONAL;
static void *PARAMETER = (void *)&PARAMETER;

static Type ERROR = { .type = TYPE_ERROR, .fixed = true };

static Value STATIC_NIL = NIL;

enum { LOW_FUEL = 5, MAX_FUEL = 9999999 };
static int FUEL = MAX_FUEL;

static int ConvertUnbound = 0;

static bool
IsSolved(Type const *t0);

static Type *
TypeOf2Op(Ty *ty, int op, Type *t0, Type *t1);

static bool
BindConstraint(Ty *ty, Constraint const *c, bool check);

static void
fixup(Ty *ty, Type *t0);

static Type *
Inst0(
        Ty *ty,
        Type *t0,
        U32Vector const *params,
        TypeVector const *args,
        bool variadic,
        bool strict
);

static Type *
Inst(Ty *ty, Type *t0, U32Vector const *params, TypeVector const *args);

static Type *
Inst1(Ty *ty, Type *t0);

static Type *
NewInst0(Ty *ty, Type *t0, TypeEnv *env);

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

static int
CountRefs(Type *t0, u32 id);

static Type *
Uniq(Ty *ty, Type *t0);

static Type *
MakeConcrete(Ty *ty, Type *t0, TypeVector *refs);

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

static bool
unify2_(Ty *ty, Type **t0, Type *t1, bool check);

static Type *
(NewObject)(Ty *ty, int class, ...);

static Type *
(NewRecord)(Ty *ty, ...);

static Type *
ClassFunctionType(Ty *ty, Type *t0);

static Type *
ToFunctionType(Ty *ty, Type *t0);

static Type *
ToRecordLikeType(Ty *ty, Type *t0);

static Type *
TagFunctionType(Ty *ty, Type *t0);

Type **
FindRecordEntry(Type const *t0, int i, char const *name);

static Type *
TupleSubscriptType(Ty *ty, Type const *t0);

static char *
VarName(Ty *ty, u32 id);

static bool
AlmostSameType(Type const *t0, Type const *t1);

static bool
SameType(Type const *t0, Type const *t1);

static bool
UnifyX(Ty *ty, Type *t0, Type *t1, bool super, bool check);

static void
Unify(Ty *ty, Type *t0, Type *t1, bool super);

static Type *
InferCall0(
        Ty *ty,
        expression_vector const *args,
        expression_vector const *kwargs,
        StringVector const *kws,
        Type *t0,
        bool strict
);

static Type *
MakeConcrete(Ty *ty, Type *t0, TypeVector *refs);

static bool
TryProgress(Ty *ty);

Type *TYPE_INT;
Type *TYPE_FLOAT;
Type *TYPE_BOOL;
Type *TYPE_STRING;
Type *TYPE_REGEX;
Type *TYPE_REGEXV;
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
static int CurrentDepth = 0;

static struct itable VarNameTable;
static struct itable FixedVarNameTable;
static int VarLetter = 'a';
static int VarNumber = 0;
static U32Vector FixedTypeVars;


// ================================
static u32 CurrentLevel = 0;
static vec(usize) WorkIndex;
static ConstraintVector ToSolve;
static vec(Expr *) FunStack;
// ================================


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
                TypeError("low fuel..");
                EnableLogging = 1;
        }

        return FUEL > 0;
}

#define EnterScope() do {               \
        xvP(WorkIndex, vN(ToSolve));    \
        CurrentLevel += 1;              \
} while (0)

#define LeaveScope() do {       \
        CurrentLevel -= 1;      \
        SolveDeferred(ty);      \
} while (0)

inline static char *
mkcstr(Ty *ty, Value const *v)
{
        if (v != NULL && v->type == VALUE_STRING) {
                char *s = amA(v->bytes + 1);

                memcpy(s, v->str, v->bytes);
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

inline static void
ClearEnv(TypeEnv *env)
{
        itable_clear(&env->vars);
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
                return (v == NULL) ? LookEnv(ty, env->parent, id)
                     : (v->type == VALUE_NIL) ? NULL
                     : v->ptr;
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
        u64 time;
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

static TypePairVector TimingMemo;

inline static int
GetTimingEntry(Ty *ty, Type const *t0, Type const *t1)
{
        static TypeEnv env = {0};

        ClearEnv(&env);

        for (int i = 0; i < vN(TimingMemo); ++i) {
                TypePair const *pair = v_(TimingMemo, i);
                if (AlmostSameType(pair->t0, t0) && AlmostSameType(pair->t1, t1)) {
                        return i;
                }
        }

        xvP(
                TimingMemo,
                ((TypePair){
                        .t0 = NewInst0(ty, (Type *)t0, &env),
                        .t1 = NewInst0(ty, (Type *)t1, &env),
                        .time = 0
                })
        );

        return vN(TimingMemo) - 1;
}

static int
TimeEntryCmp(void const *_a, void const *_b)
{
        TypePair const *a = _a;
        TypePair const *b = _b;
        if (a->time > b->time) {
                return -1;
        } else {
                return a->time != b->time;
        }
}

void
DumpTypeTimingInfo(Ty *ty)
{
        qsort(vv(TimingMemo), vN(TimingMemo), sizeof (TypePair), TimeEntryCmp);

        u64 total = 0;

        for (int i = 0; i < vN(TimingMemo); ++i) {
                TypePair const *ent = v_(TimingMemo, i);

                if (ent->time * 100 < total) {
                        break;
                }

                printf(
                        "%s===%s %s%.1fms%s %s===%s\n",
                        TERM(95),
                        TERM(0),
                        TERM(92),
                        ent->time / 1.0e6,
                        TERM(0),
                        TERM(95),
                        TERM(0)
                );
                printf("  %s\n", ShowType(ent->t0));
                printf("  %s\n", ShowType(ent->t1));

                total += ent->time;
        }
}

static void
AddConstraint(Ty *ty, Type *t0, Type *t1)
{
        if (!ENABLED) {
                return;
        }

        Expr const *fun = TyCompilerState(ty)->func;

        if (fun == NULL) {
                TypeError("lowkey type shit");
        }

        ConstraintVector *cons = &fun->_type->constraints;

        avP(
                *cons,
                ((Constraint){
                        .type = TC_SUB,
                        .t0 = t0,
                        .t1 = t1
                })
        );
}

inline static u64
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

inline static Type *
Relax(Type const *t0)
{
        switch (TypeType(t0)) {
        case TYPE_INTEGER:
                return TYPE_INT;
        }

        return (Type *)t0;
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

inline static bool
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
IsNilT(Type const *t0)
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
(NewRecord)(Ty *ty, ...)
{
        Type *t0 = NewType(ty, TYPE_TUPLE);

        Type *t1;
        char const *name;

        va_list ap;
        va_start(ap, ty);

        while ((name = va_arg(ap, char const *)) != NULL) {
                t1 = va_arg(ap, Type *);
                AddEntry(t0, t1, name);
        }

        va_end(ap);

        return t0;
}

static Type *
(NewTuple)(Ty *ty, ...)
{
        Type *t0 = NewType(ty, TYPE_TUPLE);

        Type *t1;

        va_list ap;
        va_start(ap, ty);

        while ((t1 = va_arg(ap, Type *)) != NULL) {
                AddEntry(t0, t1);
        }

        va_end(ap);

        return t0;
}

static Type *
(NewUnion)(Ty *ty, ...)
{
        Type *t0 = NewType(ty, TYPE_UNION);

        Type *t1;

        va_list ap;
        va_start(ap, ty);

        while ((t1 = va_arg(ap, Type *)) != NULL) {
                avP(t0->types, t1);
        }

        va_end(ap);

        return t0;
}

static Type *
(NewIntersect)(Ty *ty, ...)
{
        Type *t0 = NewType(ty, TYPE_INTERSECT);

        Type *t1;

        va_list ap;
        va_start(ap, ty);

        while ((t1 = va_arg(ap, Type *)) != NULL) {
                avP(t0->types, t1);
        }

        va_end(ap);

        return t0;
}

static Type *
(NewList)(Ty *ty, ...)
{
        Type *t0 = NewType(ty, TYPE_LIST);

        Type *t1;

        va_list ap;
        va_start(ap, ty);

        while ((t1 = va_arg(ap, Type *)) != NULL) {
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
        bool param = false;

        va_list ap;
        va_start(ap, ty);

        while ((t2 = va_arg(ap, Type *)) != NULL) {
                if (t2 == OPTIONAL) {
                        optional = true;
                } else if (t2 == NAMED) {
                        name = va_arg(ap, char const *);
                } else if (t2 == PARAMETER) {
                        param = true;
                } else if (param) {
                        avP(t0->bound, t2->id);
                        param = false;
                } else if (t1 == NULL) {
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

        t0->class = class_get(ty, class);

        while ((t1 = va_arg(ap, Type *)) != NULL) {
                avP(t0->args, t1);
        }

        va_end(ap);

        return t0;
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
NewStrictVar(Ty *ty)
{
        Type *t0 = NewVar(ty);
        t0->fixed = true;

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
CloneType(Ty *ty, Type const *t0)
{
        Type *t;
        if (t0 == NULL) {
                t = NULL;
        } else {
                t = amA(sizeof *t);
                *t = *t0;
                t->fixed = false;
                t->src = t0->src;
                TypeAllocCounter += 1;
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
FlattenTypeSequence(
        Ty *ty,
        TypeVector *types,
        ConstStringVector *names,
        BoolVector *required
)
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
        BoolVector flat_required = {0};

        for (int i = 0; i < vN(*types); ++i) {
                Type *t0 = ResolveVar(v__(*types, i));
                if (TypeType(t0) == TYPE_SEQUENCE) {
                        avPv(flat, t0->types);
                        if (names != NULL) {
                                while (vN(flat_names) < vN(flat)) {
                                        avP(flat_names, NULL);
                                }
                        }
                        if (required != NULL) {
                                while (vN(flat_required) < vN(flat)) {
                                        avP(flat_required, NULL);
                                }
                        }
                } else {
                        avP(flat, v__(*types, i));
                        if (names != NULL) {
                                avP(flat_names, v__(*names, i));
                        }
                        if (required != NULL) {
                                avP(flat_required, v__(*required, i));
                        }
                }
        }

        FlattenTypeSequence(
                ty,
                &flat,
                (names != NULL) ? &flat_names : NULL,
                (required != NULL) ? &flat_required : NULL
        );

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
                return FlattenTypeSequence(ty, &t0->types, &t0->names, &t0->required);
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                return FlattenTypeSequence(ty, &t0->types, NULL, NULL);
        case TYPE_ALIAS:
        case TYPE_OBJECT:
                return FlattenTypeSequence(ty, &t0->args, NULL, NULL);
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
                XXTLOG("Reduce():");
                XXTLOG("    %s", ShowType(t0));
                XXTLOG("    %s", ShowType(t1));
        }

        return t1;
}

static Type *
CoalescePatterns(Ty *ty, Type const *t0)
{
        Type *t1 = CloneType(ty, t0);
        v00(t1->types);

        TypeEnv env = {0};

        for (int i = 0; i < vN(t0->types); ++i) {
                bool keep = true;
                for (int j = 0; j < vN(t1->types); ++j) {
                        ClearEnv(&env);
                        Type *u0 = NewInst0(ty, v__(t0->types, i), &env);
                        Type *u1 = NewInst0(ty, v__(t1->types, j), &env);
                        if (UnifyX(ty, u1, u0, true, false)) {
                                keep = false;
                                break;
                        }
                }
                if (keep) {
                        avP(t1->types, v__(t0->types, i));
                } else {
                        Unify(ty, t1, v__(t0->types, i), true);
                }
        }

        XXTLOG("CoalescePatterns():");
        XXTLOG("    %s", ShowType(t0));
        XXTLOG("    %s", ShowType(t1));

        return (vN(t1->types) == 1) ? v__(t1->types, 0) : t1;
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

static void
ExtractArgs(Ty *ty, Expr const *e, TypeVector *args, TypeVector *kwargs, StringVector *kws)
{
        expression_vector const *_args;
        expression_vector const *_kwargs;

        switch (e->type) {
        case EXPRESSION_FUNCTION_CALL:
                _args = &e->args;
                _kwargs = &e->kwargs;
                *kws = e->kws;
                break;

        case EXPRESSION_METHOD_CALL:
                _args = &e->method_args;
                _kwargs = &e->method_kwargs;
                *kws = e->method_kws;
                break;

        default:
                UNREACHABLE();
        }

        for (int i = 0; i < vN(*_args); ++i) {
                avP(*args, v__(*_args, i)->_type);
        }

        for (int i = 0; i < vN(*_kwargs); ++i) {
                avP(*kwargs, v__(*_kwargs, i)->_type);
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
        return (t0 != NULL)
            && (t0->type == TYPE_OBJECT)
            && (t0->class->i != CLASS_TOP)
            && (t0->class->type->type == TYPE_TAG);
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

inline static bool
IsTuple(Type const *t0)
{
        if (TypeType(t0) != TYPE_TUPLE) {
                return false;
        }

        for (int i = 0; i < vN(t0->types); ++i) {
                if (v__(t0->names, i) != NULL) {
                        return false;
                }
        }

        return true;
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
IsTupleLike(Type const *t0)
{
        t0 = ResolveVar(t0);

        switch (TypeType(t0)) {
        case TYPE_TUPLE:
                return IsTuple(t0);

        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!IsTupleLike(v__(t0->types, i))) {
                                return false;
                        }
                }
                return true;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (IsTupleLike(v__(t0->types, i))) {
                                return true;
                        }
                }
                return false;
        }

        return false;
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
AlmostSameType(Type const *t0, Type const *t1)
{
        TLOG("SameType():");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s\n", ShowType(t1));

        if (t0 == t1) {
                return true;
        }

        while (IsBoundVar(t0) && IsBoundVar(t1)) {
                t0 = t0->val;
                t1 = t1->val;
        }

        switch (PackTypes(t0, t1)) {
        case PAIR_OF(TYPE_VARIABLE):
                return (t0->id == t1->id) || (CanBind(t0) && CanBind(t1));

        case PAIR_OF(TYPE_OBJECT):
        case PAIR_OF(TYPE_CLASS):
                if (t0->class != t1->class || vN(t0->args) != vN(t1->args)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->args); ++i) {
                        if (!AlmostSameType(v__(t0->args, i), v__(t1->args, i))) {
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
                        if (!AlmostSameType(v__(t0->types, i), v__(t1->types, i))) {
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
                        if (!AlmostSameType(v__(t0->types, i), v__(t1->types, i))) {
                                return false;
                        }
                }
                return true;

        case PAIR_OF(TYPE_TUPLE):
                if (vN(t0->types) != vN(t1->types)) {
                        return false;
                }
                if (!AlmostSameType(t0->repeat, t1->repeat)) {
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
                        if (!AlmostSameType(v__(t0->types, i), v__(t1->types, i))) {
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
                if (vN(t0->constraints) != vN(t1->constraints)) {
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
                        if (!AlmostSameType(p0->type, p1->type)) {
                                return false;
                        }
                }
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        Constraint const *c0 = v_(t0->constraints, i);
                        Constraint const *c1 = v_(t1->constraints, i);
                        if (c0->type != c1->type) {
                                return false;
                        }
                        if (
                                !AlmostSameType(c0->t0, c1->t0)
                             || !AlmostSameType(c0->t1, c1->t1)
                             || !AlmostSameType(c0->t2, c1->t2)
                        ) {
                                return false;
                        }
                }
                return AlmostSameType(t0->rt, t1->rt);

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
                        if (!AlmostSameType(v__(t0->args, i), v__(t1->args, i))) {
                                return false;
                        }
                }
                return AlmostSameType(t0->_type, t1->_type);
        }

        return false;
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
                if (!SameType(t0->repeat, t1->repeat)) {
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
                        if (IsRequired(t0, i) != IsRequired(t1, i)) {
                                return false;
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
                if (vN(t0->constraints) != vN(t1->constraints)) {
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
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        Constraint const *c0 = v_(t0->constraints, i);
                        Constraint const *c1 = v_(t1->constraints, i);
                        if (c0->type != c1->type) {
                                return false;
                        }
                        if (
                                !SameType(c0->t0, c1->t0)
                             || !SameType(c0->t1, c1->t1)
                             || !SameType(c0->t2, c1->t2)
                        ) {
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

        if (IsNilT(t0)) {
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
                c = class_get(ty, ClassOfType(ty, t0));
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

static int
CountRefs(Type *t0, u32 id)
{
        if (IsBottom(t0)) {
                return 0;
        }

        int n = 0;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (IsUnboundVar(t0)) {
                        n = (t0->id == id);
                } else {
                        n = CountRefs(t0->val, id);
                }
                break;

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                n = CountRefs(t0->val, id);
                break;

        case TYPE_TUPLE:
                n += CountRefs(t0->repeat, id);
        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                for (int i = 0; i < vN(t0->types); ++i) {
                        n += CountRefs(v__(t0->types, i), id);
                }
                break;

        case TYPE_FUNCTION:
                n += CountRefs(t0->rt, id);
                for (int i = 0; i < vN(t0->params); ++i) {
                        n += CountRefs(v_(t0->params, i)->type, id);
                }
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        Constraint const *c = v_(t0->constraints, i);
                        n += CountRefs(c->t0, id);
                        n += CountRefs(c->t1, id);
                        n += CountRefs(c->t2, id);
                }
                break;

        case TYPE_OBJECT:
        case TYPE_COMPUTED:
        case TYPE_CLASS:
        case TYPE_ALIAS:
                for (int i = 0; i < vN(t0->args); ++i) {
                        n += CountRefs(v__(t0->args, i), id);
                }
                break;
        }

        return n;
}

static bool
RefersTo(Type *t0, u32 id)
{
        return CountRefs(t0, id) > 0;
}

inline static bool
TypeVecContainsAddr(TypeVector const *types, Type const *t0)
{
        for (int i = 0; i < vN(*types); ++i) {
                if (t0 == v__(*types, i)) {
                        return true;
                }
        }

        return false;
}

inline static bool
VecContainsSub(Ty *ty, TypeVector const *types, Type const *t0)
{
        for (int i = 0; i < vN(*types); ++i) {
                if (type_check(ty, (Type *)t0, v__(*types, i))) {
                        return true;
                }
        }

        return false;
}

inline static bool
VecContainsSuper(Ty *ty, TypeVector const *types, Type const *t0)
{
        for (int i = 0; i < vN(*types); ++i) {
                if (type_check(ty, v__(*types, i), (Type *)t0)) {
                        return true;
                }
        }

        return false;
}

static bool
ContainsType(Ty *ty, Type const *t0, Type const *t1)
{
        switch (TypeType(t0)) {
        case TYPE_UNION:
                return VecContainsSuper(ty, &t0->types, t1);

        case TYPE_INTERSECT:
                return VecContainsSub(ty, &t0->types, t1);
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

        if (!ENABLED) {
                return t0;
        }

        switch (TypeType(t0)) {
        case TYPE_UNION:
        case TYPE_INTERSECT:
                n = vN(t0->types);
                v0(t0->types);
                for (int i = 0; i < n; ++i) {
                        Type *t00 = v__(t0->types, i);
                        if (!ContainsType(ty, t1, t00)) {
                                if (cloned) {
                                        vPx(t1->types, t00);
                                }
                        } else {
                                XXTLOG("Uniq(): %s", ShowType(t1));
                                XXTLOG("  drop: %s", ShowType(t00));
                                if (!cloned) {
                                        t1 = CloneType(ty, t1);
                                        CloneVec(t1->types);
                                        cloned = true;
                                }
                        }
                        vPx(t0->types, t00);
                }
                if (vN(t0->types) == 1) {
                        t1 = v__(t0->types, 0);
                }
                break;

        case TYPE_TUPLE:
                if (
                        (t0->repeat != NULL)
                     && (vN(t0->types) > 0)
                     && (v_L(t0->names) == NULL)
                     && type_check(ty, t0->repeat, v_L(t0->types))
                ) {
                        t0 = CloneType(ty, t0);
                        CloneVec(t0->types);
                        CloneVec(t0->names);
                        CloneVec(t0->required);
                        do {
                                vvX(t0->types);
                                vvX(t0->names);
                                vvX(t0->required);
                        } while (
                                (vN(t0->types) > 0)
                             && (v_L(t0->names) == NULL)
                             && type_check(ty, t0->repeat, v_L(t0->types))
                        );
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

        if (ENABLED) {
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
                avP(t2->types, (Type *)t0);
        } else for (int i = 0; i < UnionCount(t0); ++i) {
                avP(t2->types, UnionElem(t0, i));
        }
        if (IsFixed(t1)) {
                avP(t2->types, (Type *)t1);
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
        ClassDefinition const *def = (class->def != NULL)
                                   ? &class->def->class
                                   : NULL;

        Type *t0 = NewType(ty, TYPE_OBJECT);
        t0->concrete = true;

        if (class->i == CLASS_TUPLE && def != NULL) {
                t0->type = TYPE_TUPLE;

                for (int i = 0; i < vN(def->type_params); ++i) {
                        Expr const *param = v__(def->type_params, 0);
                        if (
                                (param->symbol != NULL)
                             && SymbolIsTypeVar(param->symbol)
                        ) {
                                AddEntry(t0, param->symbol->type);
                        }
                }

                return t0;
        }

        t0->class = class;

        if (class->def != NULL) {
                for (int i = 0; i < vN(def->type_params); ++i) {
                        Type *u0 = type_resolve(
                                ty,
                                v__(def->type_params, i)
                        );
                        avP(t0->args, u0);
                }
        }

        TLOG("type_object(%s) = %s (narg=%d)", class->name, ShowType(t0), (int)vN(t0->args));

        return t0;
}

Type *
type_variable(Ty *ty, Symbol *var)
{
        xDDD();

        Type *t = NewVar(ty);
        t->val = TVAR;
        t->concrete = true;

        byte_vector name = {0};
        //dump(&name, "%s", var->identifier);
        dump(&name, "%s%u", var->identifier, t->id);
        *itable_get(ty, &FixedVarNameTable, t->id) = PTR(name.items);
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

        xDDD();

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

        class->type = t;

        if (vN(class->type->bound) == 0) {
                Type *t0 = NewVar(ty);
                if (ENABLED) {
                        t0->val = TVAR;
                        t0->concrete = true;
                        avP(t->bound, t0->id);
                }
                class->object_type = NewType(ty, TYPE_OBJECT);
                class->object_type->class = class;
                class->object_type->concrete = true;
                avP(class->object_type->args, t0);
        } else {
                avPv(t->bound, class->type->bound);
        }

        return t;
}

Type *
type_class(Ty *ty, Class *class)
{
        Type *t = NewType(ty, TYPE_CLASS);
        t->class = class;
        t->concrete = true;

        if (ENABLED && class->def != NULL) {
                for (int i = 0; i < vN(class->def->class.type_params); ++i) {
                        //Type *t0 = type_resolve(
                        //        ty,
                        //        v__(class->def->class.type_params, i)
                        //);
                        Symbol *var = v__(class->def->class.type_params, i)->symbol;
                        avP(t->bound, var->type->id);
                        t->variadic |= SymbolIsVariadic(var);

                        char *tmp = VarName(ty, var->type->id);
                        Value *v = itable_get(ty, &VarNameTable, var->type->id);
                        *v = PTR(afmt("%s::<%s>", tmp, class->name));
                }
        }

        return t;
}

Type *
type_function(Ty *ty, Expr const *e, bool tmp)
{
        xDDD();

        Type *t = NewType(ty, TYPE_FUNCTION);

        //fprintf(stderr, "================== %s ======================\n", e->name);

        U32Vector bounded = {0};
        TypeVector bounds = {0};

        if (vN(e->type_bounds) > 0 && !tmp) {
                ty->tenv = NewEnv(ty, ty->tenv);
                for (int i = 0; i < vN(e->type_bounds); ++i) {
                        TypeBound const *bound = v_(e->type_bounds, i);
                        Type *a0;
                        Type *b0;
                        Type *c0;
                        Expr const *var = bound->var;
                        if (var->type == EXPRESSION_IDENTIFIER) {
                                a0 = type_resolve(ty, var);
                                b0 = type_fixed(ty, type_resolve(ty, bound->bound));
                                avP(t->constraints, CONSTRAINT(.type = TC_SUB, .t0 = a0, .t1 = b0));
                                PutEnv(ty, ty->tenv, a0->id, b0);
                        } else {
                                int op = Expr2Op(var);
                                a0 = type_resolve(ty, var->left);
                                b0 = type_resolve(ty, var->right);
                                c0 = type_resolve(ty, bound->bound);
                                avP(t->constraints, CONSTRAINT(.type = TC_2OP, .t0 = a0, .t1 = b0, .t2 = c0, .op = op));
                                break;
                        }
                }
        }

        //Symbol *self = scope_local_lookup(ty, e->scope, "self");
        //if (self != NULL) {
        //        self->type = Inst(ty, self->type, &bounded, &bounds);
        //}

        if (e->return_type != NULL) {
                Type *rt = SeqToList(type_resolve(ty, e->return_type));
                if (e->class > -1) {
                        Class *class = class_get(ty, e->class);
                        rt = SolveMemberAccess(ty, class->object_type, rt);
                }
                rt = Inst(ty, rt, &bounded, &bounds);
                t->rt = MakeConcrete(ty, rt, NULL);
        } else {
                t->rt = tmp ? AddParam(ty, t) : NewHole(ty);
        }

        // Array[T=Array[Int]]
        //
        //   [U]() -> Array[Array[U]]  where Array[Array[Int]]: Array[U]
        //

        if (e->yield_type != NULL) {
                t->yields = type_fixed(
                        ty,
                        Inst(
                                ty,
                                type_resolve(ty, e->yield_type),
                                &bounded,
                                &bounds
                        )
                );
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
                } else {
                        p0 = type_fixed(ty, p0);
                }

                if (!tmp) {
                        if (i == e->rest) {
                                psym->type = type_fixed(ty, NewArray(p0));
                        } else if (i == e->ikwargs) {
                                psym->type = type_fixed(ty, NewDict(TYPE_STRING, p0));
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
                                                (v__(e->constraints, i) == NULL)
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

        if (!tmp && e->fn_symbol != NULL) {
                e->fn_symbol->type = t;
        }

        return t;
}

static void
GatherFree(Ty *ty, Type *t0, U32Vector *freev, U32Vector *boundv)
{
        t0 = ResolveVar(t0);

        if (t0 == NULL || t0->concrete) {
                return;
        }

        //static TypeVector visiting;
        //if (already_visiting(&visiting, t0)) {
        //        return;
        //} else {
        //        xvP(visiting, t0);
        //}

        Type *t_ = t0;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        GatherFree(ty, t0->val, freev, boundv);
                } else if (
                        (boundv == NULL || !ContainsID(boundv, t0->id))
                     && (t0->level >= CurrentLevel)
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

        case TYPE_TUPLE:
                GatherFree(ty, t0->repeat, freev, boundv);
        case TYPE_UNION:
        case TYPE_INTERSECT:
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
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        Constraint const *c = v_(t0->constraints, i);
                        GatherFree(ty, c->t0, freev, boundv);
                        GatherFree(ty, c->t1, freev, boundv);
                        GatherFree(ty, c->t2, freev, boundv);
                }
                GatherFree(ty, t0->rt, freev, boundv);
                break;
        }

        //vvX(visiting);
}

static Type *
Propagate(Ty *ty, Type *t0)
{
        static int d = 0;

        Type *t = t0;

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
        Type *t3;
        bool cloned = false;

        switch (t0->type) {
        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        t1 = Propagate(ty, t0->val);
                        if (t1 != t0->val) {
                                t0 = CloneType(ty, t0);
                                t0->concrete &= IsConcrete(t1);
                        }
                        t0->val = t1;
                } else {
                        t1 = LookEnv(ty, ty->tenv, t0->id);
                        t0 = (t1 != NULL) ? Reduce(ty, t1) : t0;
                }
                break;

        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                t1 = Propagate(ty, t0->val);
                if (t1 != t0->val) {
                        t0 = CloneType(ty, t0);
                        t0->concrete &= IsConcrete(t1);
                }
                t0->val = t1;
                break;

        case TYPE_TUPLE:
                t1 = Propagate(ty, t0->repeat);
                if (t1 != t0->repeat) {
                        t0 = CloneType(ty, t0);
                        CloneVec(t0->types);
                        cloned = true;
                }
                t0->repeat = t1;
                t0->concrete &= IsConcrete(t1);
        case TYPE_LIST:
        case TYPE_UNION:
        case TYPE_INTERSECT:
        case TYPE_SEQUENCE:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t1 = v__(t0->types, i);
                        t2 = Propagate(ty, t1);
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
                        t2 = Propagate(ty, t1);
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
                        t2 = Propagate(ty, t1);
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
                        t2 = Propagate(ty, t1);
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
                        t1 = Propagate(ty, p->type);
                        if (t1 != p->type && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->params);
                                CloneVec(t0->constraints);
                                cloned = true;
                        }
                        v_(t0->params, i)->type = t1;
                        t0->concrete &= IsConcrete(t1);
                }
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        Constraint const *c0 = v_(t0->constraints, i);
                        t1 = Propagate(ty, c0->t0);
                        t2 = Propagate(ty, c0->t1);
                        t3 = Propagate(ty, c0->t2);
                        if ((t1 != c0->t0 || t2 != c0->t1 || t3 != c0->t2) && !cloned) {
                                t0 = CloneType(ty, t0);
                                CloneVec(t0->constraints);
                                cloned = true;
                        }
                        v_(t0->constraints, i)->t0 = t1;
                        v_(t0->constraints, i)->t1 = t2;
                        v_(t0->constraints, i)->t2 = t3;
                }
                t1 = Propagate(ty, t0->rt);
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

        case TYPE_TUPLE:
                if (Occurs(ty, t0->repeat, id, level)) {
                        ret = true;
                        break;
                }
        case TYPE_UNION:
        case TYPE_INTERSECT:
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
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        Constraint const *c = v_(t0->constraints, i);
                        if (
                                Occurs(ty, c->t0, id, level)
                             || Occurs(ty, c->t1, id, level)
                             || Occurs(ty, c->t2, id, level)
                        ) {
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

        TLOG("Generalize()");
        TLOG("t0: %s", ShowType(t0));

        switch (TypeType(t0)) {
        case TYPE_FUNCTION:
                GatherFree(ty, t0, &freev, &boundv);
                for (int i = 0; i < vN(t0->bound); ++i) {
                        if (RefersTo(t0, v__(t0->bound, i))) {
                                avP(freev, v__(t0->bound, i));
                                XXTLOG("  keep %s, it does appear in %s", VarName(ty, v__(t0->bound, i)), ShowType(t0));
                        } else {
                                XXTLOG("  drop %s, it doesn't appear in %s", VarName(ty, v__(t0->bound, i)), ShowType(t0));
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
        TLOG(" => %s", ShowType(t1));

        return t1;
}

static Type *
NewInst0(Ty *ty, Type *t0, TypeEnv *env)
{
        if (CanBind(t0)) {
                Type *t1 = LookEnv(ty, env, t0->id);
                if (t1 == NULL) {
                        t1 = PutEnv(
                                ty,
                                env,
                                t0->id,
                                t0->fixed ? NewStrictVar(ty) : NewVar(ty)
                        );
                }
                return t1;
        }

        __attribute__((unused)) Type *t00 = t0;

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
                t0->repeat = NewInst0(ty, t0->repeat, env);
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
                CloneVec(t0->constraints);
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param *p = v_(t0->params, i);
                        p->type = NewInst0(ty, p->type, env);
                }
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        Constraint *c = v_(t0->constraints, i);
                        c->t0 = NewInst0(ty, c->t0, env);
                        c->t1 = NewInst0(ty, c->t1, env);
                        c->t2 = NewInst0(ty, c->t2, env);
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
                        GetExpressionModule(expr),
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

        if (!def->redpilled) {
                CompilerBlackpill(ty, t0->class->def);
        }

        if (vN(def->traits) <= i) {
                return NULL;
        }

        Type *trait0 = type_resolve(ty, v__(def->traits, i));

        if (trait0 == 0) {
                TypeError("unable to resolve traits of %s", ShowType(t0));
        }

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
        ClassDefinition const *def;

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                if (t0->class->def == NULL) {
                        *u0 = UNKNOWN;
                        *name = "";
                        return true;
                }
                def = &t0->class->def->class;
                if (i < vN(def->fields)) {
                        field = v__(def->fields, i);
                        *u0 = SolveMemberAccess(ty, t0, field->_type);
                        *name = FieldIdentifier(field)->identifier;
                        return true;
                }
                i -= vN(def->fields);
                if (i < vN(def->methods)) {
                        field = v__(def->methods, i);
                        *u0 = SolveMemberAccess(ty, t0, field->_type);
                        *name = field->name;
                        return true;
                }
                i -= vN(def->methods);
                if (i < vN(def->getters)) {
                        field = v__(def->getters, i);
                        *u0 = SolveMemberAccess(ty, t0, field->_type->rt);
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

static Type *
ResolveSuperInstance(Ty *ty, Type *t0, Class const *class)
{
        XXTLOG("ResolveSuperInstance():");
        XXTLOG("  t0: %s", ShowType(t0));
        XXTLOG("   c: %s", class->name);

        if (class->i == CLASS_OBJECT) {
                return class->object_type;
        }

        while (t0->class != class) {
                XXTLOG("t0=%s", ShowType(t0));
                if (t0->class->def == NULL) {
                        CompileError(ty, "can't unify %s before we've seen its definition", ShowType(t0));
                }
                if (!t0->class->def->class.redpilled) {
                        CompilerBlackpill(ty, t0->class->def);
                }
                if (class_is_subclass(ty, t0->class->super->i, class->i)) {
                        XXTLOG("  t0 <- super: %s", t0->class->super->name);
                        t0 = GetSuper(ty, t0);
                } else {
                        for (int i = 0;; ++i) {
                                XXTLOG("  check trait #%d", i + 1);
                                Type *trait0 = GetTrait(ty, t0, i);
                                if (trait0 == NULL) {
                                        XXTLOG("  trait is NULL");
                                }
                                if (!trait0->class->def->class.redpilled) {
                                        CompilerBlackpill(ty, trait0->class->def);
                                }
                                XXTLOG("  trait: %s", trait0->class->name);
                                if (class_is_subclass(ty, trait0->class->i, class->i)) {
                                        t0 = trait0;
                                        break;
                                }
                        }
                }
        }

        return t0;
}

static bool
TryUnifyObjects(Ty *ty, Type *t0, Type *t1, bool super)
{
        t0 = Relax(t0);
        t1 = Relax(t1);

        if (
                (TypeType(t0) == TYPE_FUNCTION)
             || (TypeType(t1) == TYPE_FUNCTION)
        ) {
                Type *f0 = ToFunctionType(ty, t0);
                Type *f1 = ToFunctionType(ty, t1);
                if (
                        (f0 != NULL)
                     && (f1 != NULL)
                     && UnifyX(ty, f0, f1, super, false)
                ) {
                        XXTLOG("TryUnifyObjects(): unified as functions");
                        return true;
                } else {
                        t0 = ToRecordLikeType(ty, t0);
                        t1 = ToRecordLikeType(ty, t1);
                }
        }

        t0 = ToRecordLikeType(ty, t0);
        t1 = ToRecordLikeType(ty, t1);

        if (StrictClassOf(t0) == CLASS_ITERABLE && IsTuple(t1)) {
                t1 = NewObject(
                        CLASS_ITERABLE,
                        (t1->repeat == NULL) ? UNKNOWN : t1->repeat
                );
        }

        if (StrictClassOf(t1) == CLASS_ITERABLE && IsTuple(t0)) {
                t0 = NewObject(
                        CLASS_ITERABLE,
                        (t0->repeat == NULL) ? UNKNOWN : t0->repeat
                );
        }

        if (IsObject(t0) && IsObject(t1)) {
                if (t0->class->def == NULL || t1->class->def == NULL) {
                        XXTLOG("TryUnifyObjects(): class def is NULL");
                        return true;
                }

                if (
                        !class_is_subclass(
                                ty,
                                super ? t1->class->i : t0->class->i,
                                super ? t0->class->i : t1->class->i
                        )
                ) {
                        return false;
                }

                if (super) {
                        t1 = ResolveSuperInstance(ty, t1, t0->class);
                } else {
                        t0 = ResolveSuperInstance(ty, t0, t1->class);
                }

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

                if (t0->class->i == CLASS_ITERABLE) {
                        if (vN(t0->args) < vN(t1->args)) {
                                UnifyX(ty, TYPE_INT, v__(t1->args, vN(t0->args)), super, false);
                        }
                        if (vN(t1->args) < vN(t0->args)) {
                                UnifyX(ty, v__(t0->args, vN(t1->args)), TYPE_INT, super, false);
                        }
                }

                XXTLOG("TryUnifyObjects(): same class, compatible args");

                return true;
        }

        if (
                TypeType(t0) == TYPE_TUPLE
             && TypeType(t1) == TYPE_TUPLE
        ) {
                Type **t2;

                if (super) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                Type *t00 = v__(t0->types, i);
                                if (CanBindVariadic(t00)) {
                                        if (i < vN(t1->types)) {
                                                Type *tail = TailTypes(ty, &t1->types, i);
                                                if (t1->repeat != NULL) {
                                                        avP(tail->types, t1->repeat);
                                                }
                                                BindVar(t00, tail);
                                                Flatten(ty, t0);
                                                break;
                                        } else if (t1->repeat != NULL) {
                                                BindVar(t00, t1->repeat);
                                                break;
                                        }
                                }
                                char const *name = v__(t0->names, i);
                                t2 = FindRecordEntry(t1, i, name);
                                if (t2 == NULL) {
                                        if (
                                                name != NULL
                                             && strcmp(name, "[]") == 0
                                        ) {
                                                if (
                                                        !UnifyX(
                                                                ty,
                                                                v__(t0->types, i),
                                                                TupleSubscriptType(ty, t1),
                                                                super,
                                                                false
                                                        )
                                                ) {
                                                        return false;
                                                }
                                        } else if (!IsRequired(t0, i)) {
                                                continue;
                                        } else if (!t1->fixed) {
                                                AddEntry(t1, v__(t0->types, i), name);
                                        } else {
                                                return false;
                                        }
                                } else if (!UnifyX(ty, v__(t0->types, i), *t2, super, false)) {
                                        if (!t0->fixed) {
                                                unify2(ty, v_(t0->types, i), *t2);
                                        } else if (!t1->fixed) {
                                                type_intersect(ty, t2, v__(t0->types, i));
                                        } else {
                                                return false;
                                        }
                                }
                        }
                } else {
                        for (int i = 0; i < vN(t1->types); ++i) {
                                Type *t11 = v__(t1->types, i);
                                if (CanBindVariadic(t11)) {
                                        if (i < vN(t0->types)) {
                                                Type *tail = TailTypes(ty, &t0->types, i);
                                                if (t0->repeat != NULL) {
                                                        avP(tail->types, t0->repeat);
                                                }
                                                BindVar(t11, tail);
                                                Flatten(ty, t1);
                                                break;
                                        } else if (t0->repeat != NULL) {
                                                BindVar(t11, t0->repeat);
                                                break;
                                        }
                                }
                                char const *name = v__(t1->names, i);
                                t2 = FindRecordEntry(t0, i, name);
                                if (t2 == NULL) {
                                        if (
                                                name != NULL
                                             && strcmp(name, "[]") == 0
                                        ) {
                                                if (
                                                        !UnifyX(
                                                                ty,
                                                                v__(t1->types, i),
                                                                TupleSubscriptType(ty, t0),
                                                                !super,
                                                                false
                                                        )
                                                ) {
                                                        return false;
                                                }
                                        } else if (!IsRequired(t1, i)) {
                                                continue;
                                        } else if (!t0->fixed) {
                                                AddEntry(t0, v__(t1->types, i), name);
                                        } else {
                                                return false;
                                        }
                                } else if (!UnifyX(ty, *t2, v__(t1->types, i), super, false)) {
                                        if (!t1->fixed) {
                                                unify2(ty, v_(t1->types, i), *t2);
                                        } else if (!t0->fixed) {
                                                type_intersect(ty, t2, v__(t1->types, i));
                                        } else {
                                                return false;
                                        }
                                }
                        }
                }

                XXTLOG("TryUnifyObjects(): unified tuples");

                return true;
        }

        if (super) {
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
                                        XXTLOG("tuple upgraded");
                                        return true;
                                } else {
                                        return false;
                                }
                        }

                        XXTLOG("Unifying field %s%s%s", TERM(93), name, TERM(0));
                        XXTLOG("  t0.%s: %s", name, ShowType(u0));
                        XXTLOG("  t1.%s: %s", name, ShowType(u1));

                        if (!UnifyX(ty, Inst1(ty, u0), Inst1(ty, u1), super, false)) {
                                return false;
                        }

                        XXTLOG("Unified field %s%s%s", TERM(93), name, TERM(0));
                        XXTLOG("  t0.%s: %s", name, ShowType(u0));
                        XXTLOG("  t1.%s: %s", name, ShowType(u1));
                }

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
                        Type *trait0 = GetTrait(ty, t0, i);

                        if (trait0 == NULL) {
                                break;;
                        }

                        if (UnifyX(ty, trait0, t1, super, false)) {
                                return true;
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

static int MaxBindDepth = 0;

static int
FindMaxBindDepth(Ty *ty, Type *t0, Type *t1)
{
        TypeEnv env = {0};

        int max_depth = -1;

        for (int i = 0; i < vN(t0->types); ++i) {
                MaxBindDepth = 0;
                ClearEnv(&env);

                Type *u0 = NewInst0(ty, v__(t0->types, i), &env);
                Type *u1 = NewInst0(ty, t1, &env);

                if (!UnifyX(ty, u0, u1, true, false)) {
                        continue;
                }

                max_depth = max(max_depth, MaxBindDepth);
        }

        return max_depth;
}

static bool
TryBind(Ty *ty, Type *t0, Type *t1, bool super)
{
        if (t0 == t1) {
                return true;
        }

        if (CanBind(t0)) {
                MaxBindDepth = max(MaxBindDepth, CurrentDepth);
                if (Occurs(ty, t1, t0->id, t0->level)) {
#if 1
                        BindVar(t0, BOTTOM);
#else
                        TypeError(
                                "can't unify:\n  %s\n  %s\n",
                                ShowType(t0),
                                ShowType(t1)
                        );
#endif
                } else if (!super || !IsAny(t1)) {
                        t0->bounded |= !super;
                        BindVar(t0, type_unfixed(ty, Relax(Reduce(ty, t1))));
                }
                return true;
        } else if (CanBind(t1)) {
                MaxBindDepth = max(MaxBindDepth, CurrentDepth);
                if (Occurs(ty, t0, t1->id, t1->level)) {
                        BindVar(t1, BOTTOM);
                } else if (super || !IsAny(t0)) {
                        t1->bounded |= super;
                        BindVar(t1, type_unfixed(ty, Relax(Reduce(ty, t0))));
                }
                return true;
        }

        return false;
}


static bool
UnifyXD(Ty *ty, Type *t0, Type *t1, bool super, bool check, bool soft)
{
#define UnifyXD(ty, t0, t1, su, ch, so) ((UnifyXD)(ty, t0, t1, su, ch, so) || ((DPRINT(check, "[%d]: %s   !%s   %s", __LINE__, ShowType(t0), (super ? ">" : "<"), ShowType(t1)), false)))

#if 1
#define OK(fmt, ...) do {               \
        XXTLOG(                         \
                "%sUnify() OK%s:" fmt,  \
                TERM(92),               \
                TERM(0) __VA_OPT__(,)   \
                __VA_ARGS__             \
        );                              \
        goto Success;                   \
} while (0)
#else
#define OK(...) goto Success;
#endif

        TypeCheckCounter += 1;

        if (!FuelCheck()) {
                return false;
        }

        if (SameType(t0, t1)) {
                DPRINT(true, "SAME TYPE");
                return true;
        }

        Type *_t0 = t0;
        Type *_t1 = t1;

        CurrentDepth += 1;

#if TYPES_LOG
        char line[1024] = {0};
        for (int i = 0; i < CurrentDepth; ++i) {
                strcat(line, i + 1 == CurrentDepth ? "====" : "    ");
        }
#endif

        char const *color;
        switch (CurrentDepth) {
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

        if (CurrentDepth == 1) {
                while (TryProgress(ty)) {
                        continue;
                }
        }

        if (IsConcrete(t0) && IsConcrete(t1)) {
                if (type_check(ty, super ? t0 : t1, super ? t1 : t0)) {
                        OK("both concrete and they type-check");
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

        if (TryBind(ty, ResolveVar(t0), t1, super)) {
                OK("TryBind() successful");
        }

        if (type_check_shallow(ty, super ? t0 : t1, super ? t1 : t0)) {
                OK("check_shallow() successful");
        }

        if (IsBoundVar(t0)) {
                if (UnifyXD(ty, t0->val, t1, super, false, soft)) {
                        OK("unified with t0->val");
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
                        OK("unified post-resolution");
                } else {
                        goto Fail;
                }
        }

        if (
                IsUnboundVar(t0)
             && IsUnboundVar(t1)
             && (t0->id == t1->id)
        ) {
                OK("same unbound variable");
                goto Success;
        }

        if (IsTVar(t0)) {
                Type *bound0 = LookEnv(ty, ty->tenv, t0->id);
                if (bound0 != NULL) {
                        t0 = Resolve(ty, bound0);
                }
        }

        if (IsTVar(t1)) {
                Type *bound1 = LookEnv(ty, ty->tenv, t1->id);
                if (bound1 != NULL) {
                        t1 = Resolve(ty, bound1);
                }
        }

        DPRINT(true, "After applying bounds:");
        DPRINT(true, "    %s", ShowType(t0));
        DPRINT(true, "    %s", ShowType(t1));

        if (IsBottom(t0) || (IsBottom(t1) && !IsFixed(t1))) {
                OK("bottom");
                goto Success;
        }

        if (IsComputed(t0) || IsComputed(t1)) {
                OK("t0 or t1 computed");
                goto Success;
        }

        //if (type_check(ty, super ? t0 : t1, super ? t1 : t0)) {
        //        OK("type_check()");
        //        goto Success;
        //}

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
                        OK("both %s; inner types unified", tags_name(ty, TagOf(t0)));
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
                                        OK("t1 is an intersection and t0 matches one of its elements: %s", ShowType(v__(t1->types, i)));
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
                        OK("t1 :> t0 is an intersection and t0 is a subtype of every element");
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
                                        OK("t0 :> t1 is a union and t1 matched an element");
                                        goto Success;
                                }
                        }
                } else {
                        bool ok = true;
                        for (int i = 0; i < vN(t0->types); ++i) {
                                ok &= UnifyXD(ty, v__(t0->types, i), t1, super, false, soft);
                        }
                        if (ok) {
                                OK("t0 <: t1 is a union and t1 matched all elements");
                                goto Success;
                        } else {
                                goto Fail;
                        }
                }
        }

        if (TypeType(t1) == TYPE_UNION) {
                if (super) {
                        bool ok = true;
                        for (int i = 0; i < vN(t1->types); ++i) {
                                ok &= UnifyXD(ty, t0, v__(t1->types, i), super, false, soft);
                        }
                        if (ok) {
                                OK("t1 union");
                                goto Success;
                        } else {
                                goto Fail;
                        }
                } else {
                        for (int i = 0; i < vN(t1->types); ++i) {
                                Type **t11 = v_(t1->types, i);
                                if (UnifyXD(ty, *t11, t0, !super, false, soft)) {
                                        for (int i = 0; i < vN(t1->types); ++i) {
                                                if (v_(t1->types, i) != t11) {
                                                        type_subtract(ty, t11, v__(t1->types, i));
                                                }
                                        }
                                        OK("t1 union !super");
                                        goto Success;
                                }
                        }
                        goto Fail;
                }
        }

        if (TypeType(t0) == TYPE_INTERSECT) {
                if (super) {
                        for (int i = 0; i < vN(t0->types); ++i) {
                                if (!UnifyXD(ty, v__(t0->types, i), t1, super, false, soft)) {
                                        goto Fail;
                                }
                        }
                        OK("t0 intersect super");
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
                                        OK("t0 intersect !super");
                                        goto Success;
                                }
                        }
                        goto Fail;
                }
        }

        if (IsTagged(t0) || IsTagged(t1)) {
                goto Fail;
        }

        if (IsAny(t0) || IsAny(t1)) {
                goto Fail;
        }

        if (IsRecordLike(t0) || IsRecordLike(t1)) {
                if (TryUnifyObjects(ty, t0, t1, super)) {
                        OK("UnifyObjects()");
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
                OK("lists");
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
                             || (super && p1 != NULL && !p1->required && IsNilT(u0))
                             || (!super && p0 != NULL && !p0->required && IsNilT(u1))
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

                if (!UnifyXD(ty, t0->rt, t1->rt, super, check, soft)) {
                        goto Fail;
                }

                for (int i = 0; i < vN(t0->constraints); ++i) {
                        if (!BindConstraint(ty, v_(t0->constraints, i), super)) {
                                goto Fail;
                        }
                }

                for (int i = 0; i < vN(t1->constraints); ++i) {
                        if (!BindConstraint(ty, v_(t1->constraints, i), super)) {
                                goto Fail;
                        }
                }

                OK("unified as function types: (%s)   and   (%s)", ShowType(t0), ShowType(t1));

                goto Success;
        }

        ConvertUnbound += check;
        bool ok;
        if (!type_check(ty, super ? t0 : t1, super ? t1 : t0)) {
                ConvertUnbound -= check;
Fail:
                ok = false;

        } else {
                OK("final type check:  (%s) and (%s)", ShowType(t0), ShowType(t1));
                ConvertUnbound -= check;
Success:
                ok = true;

                if (t0 != NULL && t1 != NULL) {
                        if (t0->src == NULL) t0->src = t1->src;
                        if (t1->src == NULL) t1->src = t0->src;
                }
        }

        CurrentDepth -= 1;

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

        return ok;

#undef OK
#undef UnifyXD
}

static bool
UnifyX(Ty *ty, Type *t0, Type *t1, bool super, bool check)
{
        TLOG("UnifyX():");
        TLOG("    %s", ShowType(t0));
        TLOG("    %s\n", ShowType(t1));

#ifdef TY_PROFILE_TYPES
        Type *q0 = (CurrentDepth > 0) ? NULL : NewInst(ty, t0);
        Type *q1 = (CurrentDepth > 0) ? NULL : NewInst(ty, t1);

        int i = (CurrentDepth == 0) ? GetTimingEntry(ty, super ? t0 : t1, super ? t1 : t0) : -1;

        static u64 worst = 0;

        u64 start = TyThreadCPUTime();
        bool ok = !ENABLED || UnifyXD(ty, t0, t1, super, false, false);
        u64 end = TyThreadCPUTime();

        if (CurrentDepth == 0) {
                v_(TimingMemo, i)->time += (end - start);
                TypeCheckTime += (end - start);
                if ((end - start) > worst) {
                        worst = (end - start);
                        printf("%llu\n  %s\n  %s\n", worst, ShowType(q0), ShowType(q1));
                }
        }
#else
        bool ok = !ENABLED || UnifyXD(ty, t0, t1, super, false, false);
#endif

        if (!ok && check && ENFORCE) {
                //EnableLogging += 1;
                UnifyXD(ty, t0, t1, super, false, false);
                type_check2(ty, super ? t0 : t1, super ? t1 : t0, true);
                //EnableLogging -= 1;
                TypeError(
                        "type mismatch"
                        FMT_MORE "found:     %s"
                        FMT_MORE "expected:  %s",
                        ShowType(super ? t1 : t0),
                        ShowType(super ? t0 : t1)
                );
        }

        return ok;
}

static void
Unify(Ty *ty, Type *t0, Type *t1, bool super)
{
        UnifyX(ty, t0, t1, super, true);
}

static Type *
TrySolve2Op(Ty *ty, int op, Type *op0, Type *t0, Type *t1, Type *t2)
{
        if (!ENABLED) {
                return UNKNOWN;
        }

        t0 = ResolveVar(t0);
        t1 = ResolveVar(t1);
        t2 = ResolveVar(t2);

        int n_unbound = CanBind(t0)
                      + CanBind(t1)
                      + CanBind(t2);

        if (n_unbound > 1) {
                return NULL;
        }

        if (IsTVar(t0) || IsTVar(t1)) {
                for (int i = 0; i < vN(FunStack); ++i) {
                        Expr const *fun = v__(FunStack, i);
                        Type const *f0 = fun->_type;

                        if (TypeType(f0) != TYPE_FUNCTION) {
                                continue;
                        }

                        for (int i = 0; i < vN(f0->constraints); ++i) {
                                Constraint *c = v_(f0->constraints, i);
                                if (
                                        (c->type == TC_2OP)
                                     && (c->op == op)
                                     && type_check(ty, c->t0, t0)
                                     && type_check(ty, c->t1, t1)
                                ) {
                                        return c->t2;
                                }
                        }
                }
        }

        TypeEnv env = {0};

        if (IsBottom(op0)) {
                return NULL;
        }

        Expr left = { .type = EXPRESSION_NIL };
        Expr right = { .type = EXPRESSION_NIL };
        Expr *argv[] = { &left, &right };
        expression_vector args = { .items = argv, .count = 2 };
        expression_vector kwargs = {0};
        StringVector kws = {0};

        if ( // TODO: Is this actually doing anything?
                IsUnknown(t0)
             || IsUnknown(t1)
             || IsUnknown(t2)
        ) {
                UnifyX(ty, t0, UNKNOWN, true, true);
                UnifyX(ty, t1, UNKNOWN, true, true);
                UnifyX(ty, t2, UNKNOWN, true, true);
                return UNKNOWN;
        }

        t0 = Inst1(ty, t0);
        t1 = Inst1(ty, t1);
        t2 = Inst1(ty, t2);

        SCRATCH_SAVE();

        TypeVector keep = {0};
        bool need_retry = false;

        Type *r0 = NULL;

        for (int i = 0; i < UnionCount(t0); ++i) {
                Type *t00 = UnionElem(t0, i);
                for (int j = 0; j < UnionCount(t1); ++j) {
                        Type *t11 = UnionElem(t1, j);
                        Type *a0 = ANY;
                        Type *b0 = ANY;
                        Type *c0 = NULL;
                        Type *f0 = NULL;
                        for (int i = 0; i < IntersectCount(op0); ++i) {
                                ClearEnv(&env);
                                Type *_f0_i = IntersectElem(op0, i);
                                Type *f0_i = CloneType(ty, _f0_i);
                                TLOG("%sTrySolve2Op(%s%s%s)%s:", TERM(94), TERM(95), intern_entry(&xD.b_ops, op)->name, TERM(94), TERM(0));
                                TLOG("    %s", ShowType(f0_i));
                                TLOG("    %s", ShowType(t00));
                                TLOG("    %s", ShowType(t11));
                                TLOG("    %s", ShowType(t2));
                                Type *op0_i = Inst0(ty, f0_i, &f0_i->bound, NULL, false, true);
                                Type *t0_i = NewInst0(ty, t00, &env);
                                Type *t1_i = NewInst0(ty, t11, &env);
                                Type *t2_i = NewInst0(ty, t2, &env);
                                Type *a0_i = v_(op0_i->params, 0)->type;
                                Type *b0_i = v_(op0_i->params, 1)->type;
                                Type *c0_i;
                                if (
                                        CanBind(t0_i)
                                     && type_check(ty, b0_i, t1_i)
                                     && type_check(ty, t2_i, op0_i->rt)
                                ) {
                                        c0_i = op0_i->rt;
                                } else if (
                                        CanBind(t1_i)
                                     && type_check(ty, a0_i, t0_i)
                                     && type_check(ty, t2_i, op0_i->rt)
                                ) {
                                        c0_i = op0_i->rt;
                                } else {
                                        left._type = t0_i;
                                        right._type = t1_i;
                                        TLOG("%sTrySolve2Op[InferCall](%s%s%s)%s:", TERM(93), TERM(95), intern_entry(&xD.b_ops, op)->name, TERM(94), TERM(0));
                                        TLOG("F   %s", ShowType(op0_i));
                                        TLOG("L   %s", ShowType(t0_i));
                                        TLOG("R   %s", ShowType(t1_i));
                                        c0_i = InferCall0(ty, &args, &kwargs, &kws, op0_i, false);
                                        TLOG("%sTrySolve2Op(%s%s%s)%s:", TERM(94), TERM(95), intern_entry(&xD.b_ops, op)->name, TERM(94), TERM(0));
                                        TLOG("    %s", ShowType(op0_i));
                                        TLOG("    %s", ShowType(c0_i));
                                }
                                f0_i->rt = UNKNOWN;
                                if (
                                        !IsBottom(c0_i)
                                     && UnifyX(ty, t2_i, c0_i, true, false)
                                ) {
                                        XXTLOG("%sTrySolve2Op(%s%s%s)%s:", TERM(93), TERM(95), intern_entry(&xD.b_ops, op)->name, TERM(93), TERM(0));
                                        XXTLOG("    %s", ShowType(f0));
                                        XXTLOG("    %s", ShowType(f0_i));
                                        if (!TypeVecContainsAddr(&keep, _f0_i)) {
                                                svP(keep, _f0_i);
                                        }
                                        if (
                                                !need_retry
                                             && ((f0 == NULL) || type_check(ty, f0, f0_i))
                                        ) {
                                        //if (type_check(ty, a0, a0_i) && type_check(ty, b0, b0_i)) {
                                                XXTLOG("  GOOD");
                                                a0 = a0_i;
                                                b0 = b0_i;
                                                c0 = c0_i;
                                                f0 = f0_i;
                                        } else if (CanBind(t0) || CanBind(t1)) {
                                                XXTLOG("%sTrySolve2Op(%s%s%s)%s:", TERM(91), TERM(95), intern_entry(&xD.b_ops, op)->name, TERM(91), TERM(0));
                                                XXTLOG("    %s", ShowType(t0));
                                                XXTLOG("    %s", ShowType(t1));
                                                XXTLOG("    %s", ShowType(t2));
                                                XXTLOG("    %s", ShowType(op0_i));
                                                XXTLOG("    %s", ShowType(c0_i));
                                                need_retry = true;
                                        } else {
                                                XXTLOG("  %sTRY NEXT%s", TERM(96), TERM(0));
                                        }
                                }
                        }
                        if (!IsBottom(f0)) {
                                UnifyX(ty, t0, a0, false, false);
                                UnifyX(ty, t1, b0, false, false);
                                UnifyX(ty, t2, c0, true, false);
                                XXTLOG("%sTrySolve2Op(%s%s%s)%s:", TERM(92), TERM(95), intern_entry(&xD.b_ops, op)->name, TERM(92), TERM(0));
                                XXTLOG("    %s", ShowType(t0));
                                XXTLOG("    %s", ShowType(t1));
                                XXTLOG("    %s", ShowType(t2));
                                r0 = t2;
                        } else {
                                XXTLOG("%sTrySolve2Op(%s%s%s)%s:", TERM(91), TERM(95), intern_entry(&xD.b_ops, op)->name, TERM(91), TERM(0));
                                XXTLOG("    %s", ShowType(t0));
                                XXTLOG("    %s", ShowType(t1));
                                XXTLOG("    %s", ShowType(t2));
                        }
                }
        }

        XXTLOG("%sTrySolve2Op(%s%s%s)%s:", TERM(92), TERM(95), intern_entry(&xD.b_ops, op)->name, TERM(92), TERM(0));
        XXTLOG("    %s", ShowType(t0));
        XXTLOG("    %s", ShowType(t1));
        XXTLOG("    %s", ShowType(t2));

        if (vN(keep) == 1) {
                *op0 = *v_0(keep);
        } else if (vN(keep) > 1) {
                v0(op0->types);
                avPv(op0->types, keep);
        }

        SCRATCH_RESTORE();

        return r0;
}

static bool
BindConstraint(Ty *ty, Constraint const *_c, bool check)
{
        Type *t0;

#if defined(TY_PROFILE_TYPES)
        u64 start = TyThreadCPUTime();
#endif

        bool ok;

        Constraint *c = (Constraint *)_c;

        switch (c->type) {
        case TC_2OP:
                XXTLOG("BindConstraint(2op): %s", intern_entry(&xD.b_ops, c->op)->name);
                XXTLOG("    %s", ShowType(c->t0));
                XXTLOG("    %s", ShowType(c->t1));
                XXTLOG("    %s", ShowType(c->t2));
                c->t0 = Reduce(ty, c->t0);
                c->t1 = Reduce(ty, c->t1);
                c->t1 = Reduce(ty, c->t1);
                t0 = TrySolve2Op(ty, c->op, c->op0, c->t0, c->t1, c->t2);
                XXTLOG("%sBindConstraint(2op)%s: %s", TERM(92), intern_entry(&xD.b_ops, c->op)->name, TERM(0));
                XXTLOG("    %s", ShowType(c->t0));
                XXTLOG("    %s", ShowType(c->t1));
                XXTLOG("    %s", ShowType(c->t2));
                ok = (t0 != NULL);
                break;

        case TC_SUB:
                XXTLOG("BindConstraint(<:):");
                XXTLOG("    %s", ShowType(c->t0));
                XXTLOG("    %s", ShowType(c->t1));
                c->t0 = Reduce(ty, c->t0);
                c->t1 = Reduce(ty, c->t1);
                ok = !UnifyX(ty, c->t0, c->t1, true, false)
                  && !UnifyX(ty, c->t1, c->t0, false, false);
                break;

        }

#if defined(TY_PROFILE_TYPES)
        u64 end = TyThreadCPUTime();
        ((Constraint *)c)->time += (end - start);
#endif

        return ok;
}

static void
SolveDeferred(Ty *ty)
{
        while (TryProgress(ty)) {
                continue;
        }

        usize n = *vvX(WorkIndex);
        Type *f0 = vN(FunStack) == 0 ? NULL : v_L(FunStack)->_type;

        XXTLOG("SolveDeferred(): n=%zu  t0: %s", vN(ToSolve) - n, ShowType(f0));

        while (vN(ToSolve) > n) {
                Constraint c = *vvX(ToSolve);
                switch (c.type) {
                case TC_2OP:
                        if (
                                (vN(FunStack) > 0)
                             && TypeType(v_L(FunStack)->_type) == TYPE_FUNCTION
                             && (!IsSolved(c.t0) || !IsSolved(c.t1))
                        ) {
                                avP(v_L(FunStack)->_type->constraints, c);
                        } else if (
                                !IsBottom(c.t0)
                        ) {
                                CompilerPushContext(ty, c.src);
                                TypeError(
                                        "no impl. of %s%s%s for:"
                                        FMT_MORE "left:   %s"
                                        FMT_MORE "right:  %s"
                                        FMT_MORE "result: %s",
                                        TERM(95),
                                        intern_entry(&xD.b_ops, c.op)->name,
                                        TERM(0),
                                        ShowType(c.t0),
                                        ShowType(c.t1),
                                        ShowType(c.t2)
                                );
                        } else {
#if defined(TY_PROFILE_TYPES)
                                printf(
                                        "%"PRIu64" %s:%d: %s%s%s\n",
                                        c.time,
                                        GetExpressionModule(c.src),
                                        c.src->start.line + 1,
                                        TERM(92),
                                        intern_entry(&xD.b_ops, c.op)->name,
                                        TERM(0)
                                );
#endif
                        }
                        break;

                case TC_SUB:
                        Unify(ty, c.t0, c.t1, true);
                        break;
                }
        }
}

static bool
TryProgress(Ty *ty)
{
        usize n = (vN(WorkIndex) > 0) ? *vvL(WorkIndex) : 0;
        bool any = false;

        for (usize i = n; i < vN(ToSolve); ++i) {
                Constraint *c = v_(ToSolve, i);
                if (BindConstraint(ty, c, true)) {
                        any = true;
#if defined(TY_PROFILE_TYPES)
                        if (c->type == TC_2OP) {
                                printf(
                                        "%"PRIu64" %s:%d: %s%s%s\n",
                                        c->time,
                                        GetExpressionModule(c->src),
                                        c->src->start.line + 1,
                                        TERM(92),
                                        intern_entry(&xD.b_ops, c->op)->name,
                                        TERM(0)
                                );
                        }
#endif
                } else {
                        *v_(ToSolve, n) = *c;
                        n += 1;
                }
        }

        ToSolve.count = n;

        return any;
}

inline static Type *
ResolveAlias(Ty *ty, Type const *t0)
{
        if (CanResolveAlias(t0)) {
                return Inst(ty, t0->_type, &t0->bound, &t0->args);
        } else {
                return (Type *)t0;
        }

}

static Type *
ToRecordLikeType(Ty *ty, Type *t0)
{
        Type *t1;

        switch (TypeType(t0)) {
        case TYPE_CLASS:
        case TYPE_OBJECT:
        case TYPE_TUPLE:
                t1 = t0;
                break;

        case TYPE_TAG:
                t1 = class_get(ty, CLASS_TAG)->object_type;
                break;

        case TYPE_INTEGER:
                t1 = TYPE_INT;
                break;

        case TYPE_FUNCTION:
                t1 = class_get(ty, CLASS_FUNCTION)->object_type;
                break;

        default:
                t1 = class_get(ty, CLASS_OBJECT)->object_type;
                break;
        }

        return t1;
}

static Type *
ToFunctionType(Ty *ty, Type *t0)
{
        Type *t1 = NULL;

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                t1 = Inst1(ty, type_member_access_t(ty, t0, "__call__", false));
                break;

        case TYPE_TUPLE:
                t1 = Inst1(ty, RecordField(ty, t0, "__call__"));
                break;

        case TYPE_CLASS:
                t1 = ClassFunctionType(ty, t0);
                break;

        case TYPE_TAG:
                t1 = TagFunctionType(ty, t0);
                break;

        case TYPE_FUNCTION:
                t1 = t0;
                break;
        }

        return t1;
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
                        Type *arg0 = (arg->_type == NULL) ? UNKNOWN : Relax(arg->_type);
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
                                return Relax(v__(*kwargs, i)->_type);
                        }
                }
        }

        Type *t0 = (i != -1) ? PossibleArgTypes(ty, args, i)
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
             && (a0 == NONE_TYPE)
             && !type_check(ty, p0, NIL_TYPE)
        ) {
                if (p->name != NULL) {
                        TypeError(
                                "missing required argument for parameter %s%s%s of type `%s`",
                                TERM(92;1), p->name, TERM(0),
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

        if (UnifyX(ty, a0, p0, false, false)) {
                return true;
        }

        if (strict && ENFORCE) {
                //EnableLogging += 1;
                //CheckArg(ty, i, p, a0, false);
                //EnableLogging -= 1;
                if (p->name != NULL) {
                        TypeError(
                                "invalid argument type for parameter %s%s%s:"
                                FMT_MORE "given:    %s"
                                FMT_MORE "expected: %s",
                                TERM(92;1), p->name, TERM(0),
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
) {
        Type *t1;
        Type *t2;
        bool gather = false;

        vec(Expr) _argv = {0};
        expression_vector _args = {0};
        expression_vector _kwargs = {0};

        XXTLOG("InferCall(%s)", ShowType(t0));
        for (int i = 0; i < vN(*args); ++i) {
                XXTLOG("    %s\n", ShowType(v__(*args, i)->_type));
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
                        if (a0 == NONE_TYPE) {
                                if (
                                        !p->required
                                     || CheckArg(ty, i, p, NIL_TYPE, strict)
                                ) {
                                        continue;
                                }
                                return NULL;
                        }
                        if (!CheckArg(ty, i, p, a0, strict)) {
                                return NULL;
                        }
                }

                for (int i = 0; i < vN(*args); ++i) {
                        Param const *p = FindParam(i, NULL, &t0->params);
                        Type *a0 = Relax(v__(*args, i)->_type);
                        if (p != NULL && p->type != NULL) {
                                if (!CheckArg(ty, p - v_(t0->params, 0), p, a0, strict)) {
                                        return NULL;
                                }
                        } else if (ENFORCE && strict) {
                                TypeError(
                                        "argument %s%d%s has no matching parameter"
                                        FMT_MORE "argument type: %s"
                                        FMT_MORE "  callee type: %s",
                                        TERM(0), i + 1, TERM(0),
                                        ShowType(a0),
                                        ShowType(t0)
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
                                        "keyword argument %s%s%s has no matching parameter"
                                        FMT_MORE "argument type: %s"
                                        FMT_MORE "  callee type: %s",
                                        TERM(93;1), v__(*kws, i), TERM(0),
                                        ShowType(a0),
                                        ShowType(t0)
                                );
                        } else {
                                return NULL;
                        }
                }

                for (;;) {
                        bool any = false;
                        usize n = 0;

                        for (int i = 0; i < vN(t0->constraints); ++i) {
                                Constraint const *c = v_(t0->constraints, i);
                                if (BindConstraint(ty, c, true)) {
                                        any = true;
                                } else {
                                        *v_(t0->constraints, n) = *c;
                                        n += 1;
                                }
                        }

                        t0->constraints.count = n;

                        if (!any) {
                                break;
                        }
                }

                XXTLOG("InferCall()");
                XXTLOG("    %s", ShowType(t0));

                return Reduce(ty, t0->rt);

        case TYPE_CLASS:
                return InferCall0(ty, args, kwargs, kws, ClassFunctionType(ty, t0), strict);

        case TYPE_TAG:
                if (vN(*args) > 1) {
                        t2 = NewType(ty, TYPE_TUPLE);
                        for (int i = 0; i < vN(*args); ++i) {
                                AddEntry(t2, v__(*args, i)->_type);
                        }
                } else if (vN(*kws) > 0) {
                        t2 = NewType(ty, TYPE_TUPLE);
                        for (int i = 0; i < vN(*kws); ++i) {
                                AddEntry(t2, v__(*kwargs, i)->_type, v__(*kws, i));
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
                for (int i = 0; i < vN(*kws); ++i) {
                        XXTLOG("   (%s%s%s) %s", TERM(93), v__(*kws, i), TERM(0), ShowType(v__(*kwargs, i)->_type));
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
                                tmp._type = NewInst0(ty, Relax(v__(*args, i)->_type), env);
                                avP(_argv, tmp);
                        }

                        for (int i = 0; i < vN(*kwargs); ++i) {
                                tmp._type = NewInst0(ty, Relax(v__(*kwargs, i)->_type), env);
                                avP(_argv, tmp);
                        }

                        for (int i = 0; i < vN(*args); ++i) {
                                avP(_args, v_(_argv, i));
                        }

                        for (int i = 0; i < vN(*kwargs); ++i) {
                                avP(_kwargs, v_(_argv, i + vN(*args)));
                        }

                        t2 = NewInst(ty, t1);

                        Type *t3 = InferCall0(ty, &_args, &_kwargs, kws, t2, false);
                        if (t3 != NULL) {
                                XXTLOG(" OK:  %s", ShowType(t2));
                                XXTLOG("   -> %s", ShowType(t3));
                                return InferCall0(ty, args, kwargs, kws, t1, strict);
                        }
                }
                if (ENFORCE && strict) {
                        byte_vector msg = {0};
                        dump(&msg, FMT_MORE "Arguments:");
                        for (int i = 0; i < vN(*args); ++i) {
                                dump(&msg, FMT_MORE "  arg[%d]: %s", i, ShowType(Relax(v__(*args, i)->_type)));
                        }
                        for (int i = 0; i < vN(*kws); ++i) {
                                dump(
                                        &msg,
                                        FMT_MORE "  kwarg[%s%s%s]: %s",
                                        TERM(92),
                                        v__(*kws, i),
                                        TERM(0),
                                        ShowType(Relax(v__(*kwargs, i)->_type))
                                );
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
        if (IsBottom(t0)) {
                return t0;
        }

        if (IsNilT(t0)) {
                return NIL_TYPE;
        }

        Type *t;
        Type *t1;
        Type *t2;
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

        for (int i = 0; i < vN(*args); ++i) {
                Expr *arg = v__(*args, i);
                if (arg->type == EXPRESSION_SPREAD) {
                        arg->_type = type_iterable_type(ty, arg->_type, 1);
                }
        }

        switch (t0->type) {
        case TYPE_TAG:
                if (
                        (vN(*args) == 1 && vN(*kws) == 0)
                     || (e->type == EXPRESSION_TAG_APPLICATION)
                ) {
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
                t1 = ToFunctionType(ty, t0);
                return InferCall(ty, args, kwargs, kws, t1);

        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        return type_call_t(ty, e, t0->val);
                } else {
                        t1 = NewType(ty, TYPE_FUNCTION);
                        t1->rt = NewVar(ty);
                        for (int i = 0; i < vN(*args); ++i) {
                                Type *p0 = NewVar(ty);
                                avP(t1->params, PARAM(NULL, p0, true));
                        }
                        for (int i = 0; i < vN(*args); ++i) {
                                Unify(ty, v_(t1->params, i)->type, v__(*args, i)->_type, true);
                        }
                        Unify(ty, t1, t0, false);
                        return t1->rt;
                }
        }

        return NULL;
}

Type *
type_call(Ty *ty, Expr const *e)
{
        xDDD();

        Type *t0 = type_call_t(ty, e, e->function->_type);
        dont_printf("type_call()\n");
        dont_printf("    >>> %s\n", show_expr(e));
        dont_printf("    %s\n", ShowType(t0));
        //e->function->_type = Inst1(ty, e->function->_type);
        return t0;
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

        if (false && TypeType(s0) == TYPE_UNION) {
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

static Type *
Inst0(
        Ty *ty,
        Type *t0,
        U32Vector const *params,
        TypeVector const *args,
        bool variadic,
        bool strict
) {
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
                        Type *u0 = NewVar(ty);
                        u0->fixed = strict;
                        avP(vars, u0);
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
        return Inst0(ty, t0, params, args, t0 != NULL && t0->variadic, false);
}

static Type *
Inst1(Ty *ty, Type *t0)
{
        Type *t1 = t0;

        switch (TypeType(t0)) {
        case TYPE_FUNCTION:
                t1 = Inst0(ty, t0, &t0->bound, NULL, t0->variadic, false);
                if (t1 == t0 && vN(t1->bound) > 0) {
                        t1 = CloneType(ty, t1);
                }
                v00(t1->bound);
                break;

        case TYPE_OBJECT:
                if (IsAny(t0)) {
                        break;
                }
                t1 = Inst0(ty, t0, &t0->class->type->bound, NULL, t0->variadic, false);
                if (t1 == t0) {
                        t1 = CloneType(ty, t1);
                }
                v00(t1->bound);
                break;


        case TYPE_INTERSECT:
        case TYPE_UNION:
                t1 = CloneType(ty, t0);
                CloneVec(t1->types);
                for (int i = 0; i < vN(t1->types); ++i) {
                        *v_(t1->types, i) = Inst1(ty, v__(t1->types, i));
                }
                break;
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

        if (TypeType(t0) != TYPE_OBJECT || IsAny(t0)) {
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
                if (IsObject(tr0)) {
                        t = Inst(
                                ty,
                                t,
                                &tr0->class->type->bound,
                                &tr0->args
                        );
                } else {
#ifndef TY_RELEASE
                        TypeError(
                                "class trait resolved to non-object type:  %s  |   %s",
                                ShowType(tr0),
                                show_expr(trait)
                        );
#else
                        UNREACHABLE("class trait resolved to non-object type");
#endif
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

        XXTLOG("SolveMemberAccess():");
        XXTLOG("    %s", ShowType(t0));
        XXTLOG("    %s", ShowType(t1));
        XXTLOG("    %s\n", ShowType(t));

        return t;
}

static Type *
type_member_access_t_(Ty *ty, Type const *t0, char const *name, bool strict)
{
        t0 = Resolve(ty, t0);

        if (
                IsNilT(t0)
             || IsBottom(t0)
             || IsAny(t0)
        ) {
                return (Type *)t0;
        }

        Class *c;
        Expr *f;
        expression_vector ops = {0};

        Type *t1 = NULL;
        Type *t2;

        switch (TypeType(t0)) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        t2 = type_member_access_t_(ty, v__(t0->types, i), name, false);
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
                        t2 = type_member_access_t_(ty, v__(t0->types, i), name, false);
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
                if (t1 == NULL && strcmp(name, "[]") == 0) {
                        return TupleSubscriptType(ty, t0);
                }
                if (ENFORCE && strict && t1 == NULL) {
                        goto NotFound;
                }
                return t1;

        case TYPE_CLASS:
        case TYPE_TAG:
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
                if (t1 != NULL) {
                        return SolveMemberAccess(ty, t0, t1);
                }

                if (t0->type == TYPE_CLASS) {
                        t0 = class_get(ty, CLASS_CLASS)->object_type;
                } else {
                        t0 = class_get(ty, CLASS_TAG)->object_type;
                }
                /* fallthrough */

        case TYPE_OBJECT:
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
                if (
                        (t1 == NULL)
                     && ((f = FindMethod(t0->class, "__missing__")) != NULL)
                ) {
                        t1 = f->_type->rt;
                }
                if (
                        ENFORCE
                     && strict
                     && (t1 == NULL)
                     && (vN(t0->class->def->class.fields) > 0) // FIXME: remove crutch eventually
                ) {
                        goto NotFound;
                }
                return SolveMemberAccess(ty, t0, t1);

        case TYPE_VARIABLE:
                if (IsBoundVar(t0)) {
                        return type_member_access_t_(ty, t0->val, name, strict);
                } else if (!IsTVar(t0)) {
                        t1 = NewVar(ty);
                        Unify(ty, (Type *)t0, NewRecord(name, t1), true);
                        return t1;
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
        Type *t1 = type_member_access_t_(ty, Relax(t0), name, strict);
        TLOG("MemberAccess(%s):", name);
        TLOG("  t0:  %s", ShowType(t0));
        TLOG("  t1:  %s\n", ShowType(t1));
        return t1;
}

Type *
type_member_access(Ty *ty, Expr const *e)
{
        xDDD();

        if (e->type == EXPRESSION_DYN_MEMBER_ACCESS) {
                return NewVar(ty);
        }

        Type *t0 = type_member_access_t(ty, e->object->_type, e->member->identifier, false);
        Type *t1;

        if (t0 == NULL) {
                if (e->maybe) {
                        return NIL_TYPE;
                } else if (!IsFixed(e->object->_type)) {
                        t0 = NewVar(ty);
                        t1 = NewType(ty, TYPE_TUPLE);
                        AddEntry(t1, t0, e->member->identifier);
                        type_intersect(ty, &e->object->_type, t1);
                } else {
                        type_member_access_t(ty, e->object->_type, e->member->identifier, true);
                }
        }

        return t0;
}

Type *
type_method_call_t(Ty *ty, Expr const *e, Type *t0, char const *name)
{
        t0 = Resolve(ty, t0);

        if (IsNilT(t0)) {
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
        case TYPE_CLASS:
        case TYPE_TAG:
        case TYPE_VARIABLE:
        case TYPE_TUPLE:
        case TYPE_FUNCTION:
        case TYPE_INTEGER:
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
        xDDD();

        Expr _method;

        Type *t1 = type_method_call_t(
                ty,
                &(Expr){
                        .type = EXPRESSION_METHOD_CALL,
                        .method = &_method
                },
                t0,
                name
        );

        return t1;
}

Type *
type_method_call(Ty *ty, Expr const *e)
{
        xDDD();

        return type_method_call_t(
                ty,
                e,
                Relax(e->object->_type),
                e->method->identifier
        );
}

Type *
type_tagged(Ty *ty, int tag, Type *t0)
{
        xDDD();

        Type *t1 = NewType(ty, TYPE_OBJECT);

        t1->class = tags_get_class(ty, tag);
        avP(t1->args, type_unfixed(ty, t0));

        t1->concrete = IsConcrete(t0);

        return t1;
}

Type *
type_generator(Ty *ty, Expr const *e)
{
        xDDD();

        Type *t0 = NewType(ty, TYPE_OBJECT);

        t0->class = class_get(ty, CLASS_GENERATOR);
        avP(t0->args, TypeArg(e->_type->rt, 0));

        return t0;
}

Type *
type_slice_t(Ty *ty, Type *t0, Type *t1, Type *t2, Type *t3)
{
        xDDD();

        Type *t4 = NewVar(ty);
        Type *t5 = NewRecord("[;;]", NewFunction(t1, t2, t3, t4));

        UnifyX(ty, t5, t0, false, false)
     || UnifyX(ty, t0, t5, false, true);

        return t4;
}

Type *
type_subscript_t(Ty *ty, Type *t0, Type *t1)
{
        Type *t2 = NewVar(ty);
        Type *t3 = NewRecord("[]", NewFunction(t1, t2));

        UnifyX(ty, t0, t3, false, false)
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
        xDDD();

        return type_subscript_t(
                ty,
                e->container->_type,
                e->subscript->_type
        );
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
check_entry(Ty *ty, Type *t0, int i, Type *t1, bool required, bool need)
{
        if (IsBottom(t0)) {
                return false;
        }

        switch (t0->type) {
        case TYPE_UNION:
                for (int ii = 0; ii < vN(t0->types); ++ii) {
                        if (!check_entry(ty, v__(t0->types, ii), i, t1, required, need)) {
                                return false;
                        }
                }
                return true;

        case TYPE_INTERSECT:
                for (int ii = 0; ii < vN(t0->types); ++ii) {
                        if (check_entry(ty, v__(t0->types, ii), i, t1, required, false)) {
                                return true;
                        }
                }
                return false;

        case TYPE_TUPLE:
                return (vN(t0->types) > i)  ? type_check_x(ty, v__(t0->types, i), t1, need)
                     : (t0->repeat != NULL) ? type_check_x(ty, t0->repeat, t1, need)
                     : !required;
        }

        return false;
}

static bool
check_field(
        Ty *ty,
        Type *t0,
        char const *name,
        Type *t1,
        bool required,
        bool need
)
{
        t0 = ResolveVar(t0);

        if (IsBottom(t0)) {
                return false;
        }

        Type *t2;

        switch (t0->type) {
        case TYPE_UNION:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (!check_field(ty, v__(t0->types, i), name, t1, required, need)) {
                                return false;
                        }
                }
                return true;

        case TYPE_INTERSECT:
                for (int i = 0; i < vN(t0->types); ++i) {
                        if (check_field(ty, v__(t1->types, i), name, t1, required, false)) {
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
                return !required;

        case TYPE_OBJECT:
                t2 = type_member_access_t_(ty, t0, name, false);
                if (t2 != NULL) {
                        return type_check_x(ty, t2, t1, need);
                }
                return !required;
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

static bool
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

        if (TypeType(t0) == TYPE_NONE || TypeType(t1) == TYPE_NONE) {
                return true;
        }

        if (t0->type == TYPE_TAG && t1->type == TYPE_TAG) {
                return TagOf(t0) == TagOf(t1);
        }

        if (
                (t0->type == TYPE_OBJECT)
             && (t0->class->i == CLASS_CLASS)
             && (t1->type == TYPE_CLASS)
        ) {
                return true;
        }

        if (
                (t0->type == TYPE_OBJECT)
             && (t0->class->i == CLASS_FUNCTION)
             && IsCallable(t1)
        ) {
                return true;
        }

        if (
                (t1->type == TYPE_OBJECT)
             && (t1->class->i == CLASS_FUNCTION)
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

        if (IsUnboundVar(t0) || IsUnboundVar(t1)) {
                return false;
        }

        if (IsTagged(t0) || IsTagged(t1)) {
                if (!IsTagged(t0) || !IsTagged(t1) || TagOf(t0) != TagOf(t1)) {
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
                if (IsTupleLike(t0) != IsTupleLike(t1)) {
                        return false;
                }
                for (int i = 0; i < vN(t0->types); ++i) {
                        char const *name = v__(t0->names, i);
                        Type *t2 = (name != NULL)
                                 ? RecordField(ty, t1, name)
                                 : RecordElem(t1, i);
                        if (t2 == NULL && !IsRequired(t0, i)) {
                                continue;
                        }
                        if (t2 == NULL || !type_check_x(ty, v__(t0->types, i), t2, need)) {
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
                if (IsTupleLike(t0) != IsTupleLike(t1)) {
                        return false;
                }
                for (int i = 0; i < vN(t1->types); ++i) {
                        char const *name = v__(t1->names, i);
                        if (
                                (name == NULL)
                              ? !check_entry(ty, t0, i, v__(t1->types, i), IsRequired(t1, i), need)
                              : !check_field(ty, t0, name, v__(t1->types, i), IsRequired(t1, i), need)
                        ) {
                                DPRINT(name && need, "Field(%s) %s.%s != %s", name, ShowType(t0), name, ShowType(v__(t1->types, i)));
                                DPRINT(!name && need, "Field(%d) %s.%d != %s", i, ShowType(t0), i, ShowType(v__(t1->types, i)));
                                return false;
                        }
                }
                return true;
        }

        if (IsObject(t0)) {
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
                TLOG("Check functions:");
                TLOG("  %s", ShowType(t0));
                TLOG("  %s", ShowType(t1));
                bool t0_allows_extra = false;
                bool t1_allows_extra = false;
                bool t0_allows_extra_kw = false;
                bool t1_allows_extra_kw = false;
                for (int i = 0; i < vN(t0->params) && i < vN(t1->params); ++i) {
                        Param const *pp0 = v_(t0->params, i);
                        Param const *pp1 = v_(t1->params, i);
                        t0_allows_extra    |= pp0->rest;
                        t0_allows_extra_kw |= pp0->kws;
                        t1_allows_extra    |= pp1->rest;
                        t1_allows_extra_kw |= pp1->kws;
                        if (
                                (pp0->rest ^ pp1->rest)
                             || (pp0->kws ^ pp1->kws)
                        ) {
                                continue;
                        }
                        Type *p0 = pp0->type;
                        Type *p1 = pp1->type;
                        if (!type_check_x(ty, p1, p0, need)) {
                                return false;
                        }
                }
                for (int i = vN(t1->params); i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
                        if (p->required) {
                                return false;
                        }
                        if (
                                (p->rest && !t0_allows_extra)
                             || (p->kws  && !t0_allows_extra_kw)
                        ) {
                                return false;
                        }
                }
                for (int i = vN(t0->params); i < vN(t1->params); ++i) {
                        Param const *p = v_(t1->params, i);
                        if (p->required) {
                                return false;
                        }
                        if (
                                (p->rest && !t1_allows_extra)
                             || (p->kws  && !t1_allows_extra_kw)
                        ) {
                                return false;
                        }
                }
                Type *r0 = t0->rt;
                Type *r1 = t1->rt;
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
                XXXTLOG("%stype_check_x():%s", ok ? TERM(92) : TERM(91), TERM(0));
                XXXTLOG("    %s", ShowType(t0));
                XXXTLOG("    %s", ShowType(t1));
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

        ok = !ENABLED || type_check_x(ty, t0, t1, false);

        TLOG("%stype_check_x():%s", ok ? TERM(92) : TERM(91), TERM(0));
        TLOG("    %s", ShowType(t0));
        TLOG("    %s", ShowType(t1));

        if (false && checks > 8 && IsConcrete(t0) && IsConcrete(t1)) {
                AddMemo(&memo, t0, t1, ok);
        }

        return ok;
}

Type *
type_tuple(Ty *ty, Expr const *e)
{
        xDDD();

        Type *t0 = NewType(ty, TYPE_TUPLE);
        t0->fixed = true;

        for (int i = 0; i < vN(e->es); ++i) {
                Type *u0 = NewVar(ty);
                AddEntry(t0, u0, v__(e->names, i), false);
                BindVar(u0, (v__(e->es, i)->_type));
        }

        return t0;
}

Type *
type_list(Ty *ty, Expr const *e)
{
        xDDD();

        Type *t0 = NewType(ty, TYPE_LIST);

        for (int i = 0; i < vN(e->es); ++i) {
                avP(t0->types, Relax(v__(e->es, i)->_type));
        }

        return t0;
}

Type *
type_list_from(Ty *ty, expression_vector const *es)
{
        xDDD();

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

Type *
type_dict(Ty *ty, Expr const *e)
{
        xDDD();

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
        t->class = class_get(ty, CLASS_DICT);
        avP(t->args, Relax(t0));
        avP(t->args, Relax(t1));

        return t;
}

Type *
type_array(Ty *ty, Expr const *e)
{
        xDDD();

        Type *t0 = NewVar(ty);
        Type *t1;

        if (vN(e->elements) == 1) {
                if (v__(e->elements, 0)->type == EXPRESSION_SPREAD) {
                        Unify(
                                ty,
                                t0,
                                type_iterable_type(
                                        ty,
                                        Relax(v__(e->elements, 0)->_type),
                                        1
                                ),
                                true
                        );
                } else {
                        Unify(ty, t0, v__(e->elements, 0)->_type, true);
                }
        } else if (vN(e->elements) > 1) {
                t1 = NewType(ty, TYPE_UNION);
                for (int i = 0; i < vN(e->elements); ++i) {
                        Type *u0 = Relax(v__(e->elements, i)->_type);
                        if (v__(e->elements, i)->type == EXPRESSION_SPREAD) {
                                u0 = type_iterable_type(ty, u0, 1);
                        }
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

static char const *
_show_tflags(int flags)
{
        static byte_vector buf;

        if (vC(buf) != 0) {
                *vv(buf) =  '\0';
                v0(buf);
        }

#define X(f, i)                                      \
        if (flags & (T_FLAG_ ## f)) {                \
                dump(&buf, &(" | " #f)[3*!vN(buf)]); \
        }
        TY_T_FLAGS
#undef X

        return vv(buf);
}

void
type_assign(Ty *ty, Expr *e, Type *t0, int flags)
{
        XXTLOG("assign(%s)", _show_tflags(flags));
        XXTLOG("    %s", ShowType(t0));
        XXTLOG("    %s\n", show_expr(e));

        if (!ENABLED) {
                return;
        }

        Type *t1;
        Type *t2;
        Type *t3;
        Type *t4;

        bool strict = flags & T_FLAG_STRICT;

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
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_RESOURCE_BINDING:
                if (!SymbolIsFixedType(e->symbol)) {
                        XXTLOG(
                                "type_assign(): %s : %s |= %s",
                                e->symbol->identifier,
                                ShowType(e->symbol->type),
                                ShowType(t0)
                        );
                        if (
                                (e->symbol->type == NULL || CanBind(e->symbol->type))
                             && (flags & T_FLAG_AVOID_NIL)
                             && IsNilT(t0)
                        ) {
                                t0 = type_either(ty, NewVar(ty), type_unfixed(ty, t0));
                        }
                        if (flags & T_FLAG_UPDATE) {
                                Refinement *ref = ScopeRefineVar(
                                        ty,
                                        TyCompilerState(ty)->active,
                                        e->symbol,
                                        t0
                                );
                                ref->mut = true;
                        } else {
                                unify2_(ty, &e->symbol->type, t0, strict);
                        }
                        unify2_(ty, &e->_type, t0, strict);
                        XXTLOG(
                                "type_assign(): %s |= %s    --->    %s",
                                e->symbol->identifier,
                                ShowType(t0),
                                ShowType(e->symbol->type)
                        );
                } else if (
                        !UnifyX(ty, t0, e->symbol->type, false, false)
                     && strict
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
                type_assign(ty, e->tagged, t1, flags);
                UnifyX(ty, t0, type_tagged(ty, e->symbol->tag, t1), false, strict);
                break;
        case EXPRESSION_ARRAY:
                if (vN(e->elements) == 0) {
                        break;
                } else if (vN(e->elements) == 1) {
                        t1 = NewVar(ty);
                        if (v__(e->elements, 0)->type == EXPRESSION_MATCH_REST) {
                                type_assign(ty, v__(e->elements, 0), t1, flags);
                                UnifyX(ty, t1, t0, true, strict);

                        } else {
                                type_assign(ty, v__(e->elements, 0), t1, flags);
                                UnifyX(ty, NewArray(t1), t0, true, strict);
                        }
                } else {
                        t1 = NewType(ty, TYPE_UNION);
                        for (int i = 0; i < vN(e->elements); ++i) {
                                Expr *elem = v__(e->elements, i);
                                if (elem->type == EXPRESSION_MATCH_REST) {
                                        type_assign(ty, elem, NewArray((t2 = NewVar(ty))), flags);
                                } else {
                                        type_assign(ty, elem, (t2 = NewVar(ty)), flags);
                                }
                                avP(t1->types, t2);
                        }
                        t1 = CoalescePatterns(ty, t1);
                        UnifyX(ty, NewArray(t1), t0, true, strict);
                }
                break;
        case EXPRESSION_TUPLE:
                t1 = NewType(ty, TYPE_TUPLE);
                for (int i = 0; i < vN(e->es); ++i) {
                        char const *name = v__(e->names, i);
                        if (name != NULL && strcmp(name, "*") == 0) {
                                continue;
                        }
                        if (IsFixed(v__(e->es, i)->_type)) {
                                t2 = v__(e->es, i)->_type;
                        } else {
                                t2 = NewVar(ty);
                        }
                        AddEntry(t1, t2, name, v__(e->required, i));
                        type_assign(ty, v__(e->es, i), t2, flags);
                }
                UnifyX(ty, t1, t0, true, strict);
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
                UnifyX(ty, t0, t3, true, strict);
                break;

        case EXPRESSION_CHOICE_PATTERN:
                t1 = NULL;
                for (int i = 0; i < vN(e->es); ++i) {
                        Type *var = NewVar(ty);
                        type_assign(ty, v__(e->es, i), var, flags);
                        t1 = (t1 == NULL) ? var : Either(ty, t1, var);
                }
                UnifyX(ty, t0, t1, true, strict);
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
                UnifyX(ty, t1, t0, true, strict);
                break;

        case EXPRESSION_MEMBER_ACCESS:
                t1 = NewForgivingVar(ty);
                t2 = NewRecord(e->member->identifier, t1);
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
        return Inst0(ty, (Type *)t0, params, args, false, false);
}

Type *
type_var(Ty *ty)
{
        if (ENABLED) {
                return NewVar(ty);
        } else {
                return UNKNOWN;
        }
}

Type *
type_resolve(Ty *ty, Expr const *e)
{
        xDDD();

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
                if (
                        (e->symbol == NULL)
                     && (e->xscope == NULL)
                     && !CompilerResolveExpr(ty, (Expr *)e)
                ) {
                        return NULL;
                }
                if (e->symbol == NULL) {
                        CompilerPushContext(ty, e);
                        TypeError("cannot resolve type name `%s%s%s`", TERM(93), e->identifier, TERM(0));
                }
                if (e->symbol->class != -1) {
                        t0 = NewType(ty, TYPE_OBJECT);
                        t0->class = class_get(ty, e->symbol->class);
                } else if (e->symbol->tag != -1) {
                        t0 = e->symbol->type;
                } else if (!IsBottom(e->symbol->type) && !IsHole(e->symbol->type)) {
                        t0 = e->symbol->type;
                } else if (SymbolIsTypeVar(e->symbol)) {
                        return e->symbol->type;
                } else {
                        t0 = BOTTOM;
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

        case EXPRESSION_TYPE_OF:
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
                TLOG("resolve_subscript():");
                TLOG("  %s", show_expr(e));
                TLOG("  %s", ShowType(t0));
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
                t0->fixed = true;
                for (int i = 0; i < vN(e->es); ++i) {
                        if (v__(e->es, i)->type == EXPRESSION_SPREAD) {
                                t0->repeat = type_resolve(ty, v__(e->es, i)->value);
                        } else {
                                AddEntry(
                                        t0,
                                        type_resolve(ty, v__(e->es, i)),
                                        v__(e->names, i),
                                        v__(e->required, i)
                                );
                        }
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
                t2 = type_both(ty, t0, t1);
                //if (type_check(ty, t0, t1)) {
                //        return t1;
                //}
                //if (type_check(ty, t1, t0)) {
                //        return t0;
                //}
                //t2 = NewType(ty, TYPE_INTERSECT);
                //avP(t2->types, t0);
                //avP(t2->types, t1);
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
                                Expr *param  = v__(e->left->es, i);
                                Param p = { .name = name, .required = v__(e->left->required, i) };

                                switch (param->type) {
                                case EXPRESSION_SPREAD:
                                        p.type = type_resolve(ty, param->value);
                                        p.rest = true;
                                        break;

                                case EXPRESSION_SPLAT:
                                        p.type = type_resolve(ty, param->value);
                                        p.kws = true;
                                        break;

                                default:
                                        p.type = type_resolve(ty, param);
                                        break;
                                }

                                avP(t0->params, p);
                        }
                } else {
                        avP(t0->params, PARAM(NULL, type_resolve(ty, e->left), true));
                }
                t0->rt = SeqToList(type_resolve(ty, e->right));
                return t0;

        case EXPRESSION_ARRAY:
                t0 = NewType(ty, TYPE_OBJECT);
                t0->class = class_get(ty, CLASS_ARRAY);
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
                *t0 = type_unfixed(ty, t1);
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

        return UnifyX(ty, *t0, t1, true, check);
}

void
unify2(Ty *ty, Type **t0, Type *t1)
{
        xDDDDD();
        unify2_(ty, t0, t1, true);
}

void
unify(Ty *ty, Type **t0, Type *t1)
{
        xDDDDD();

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
                return S2("⭕️");
        }

        if (IsUnknown(t0)) {
                return S2("🟢");
        }

        if (IsBottom(t0)) {
                return S2("🔴");
        }

        if (already_visiting(&visiting, t0) || vN(visiting) > 24) {
                return S2("...");
        } else {
                xvP(visiting, (Type *)t0);
        }

        if (IsFixed(t0)) {
                //dump(&buf, "!");
        }

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                if (t0->class->i < CLASS_BUILTIN_END) {
                        dump(
                                &buf,
                                "%s%s%s",
                                TERM(92;1),
                                t0->class->name,
                                TERM(0)

                        );
                } else if (IsTagged(t0)) {
                        dump(
                                &buf,
                                "%s%s%s",
                                TERM(38:2:150:173:101),
                                t0->class->name,
                                TERM(0)
                        );
                } else {
                        dump(
                                &buf,
                                "%s%s%s",
                                TERM(38:2:205:96:137;1),
                                t0->class->name,
                                TERM(0)
                        );
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
                dump(
                        &buf,
                        "%sClass[%s%s%s]%s",
                        TERM(33;1),
                        TERM(95),
                        t0->class->name != NULL ? t0->class->name : "?",
                        TERM(33;1),
                        TERM(0)
                );
                break;
        case TYPE_TAG:
                dump(
                        &buf,
                        "%s%s%s",
                        TERM(34;1),
                        t0->class->name,
                        TERM(0)
                );
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
                                                ShowType(c->t2)
                                        );
                                        break;
                                case TC_SUB:
                                        dump(
                                                &buf,
                                                "(%s : %s)",
                                                ShowType(c->t0),
                                                ShowType(c->t1)
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
                                        : !p->required ? "?"
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
#ifdef TY_DEBUG_TYPES
                dump(&buf, t0->type == TYPE_LIST ? "list" : "seq");
#endif
        case TYPE_TUPLE:
                if (is_record(t0)) {
                        dump(&buf, "%s{%s", TERM(38:2:240:158:58), TERM(0));
                        for (int i = 0; i < vN(t0->types); ++i) {
                                if (i > 0) {
                                        dump(&buf, ", ");
                                }
                                if (!IsRequired(t0, i)) {
                                        dump(&buf, "%s?%s", TERM(1;34), TERM(0));
                                }
                                if (v__(t0->names, i) == NULL) {
                                        dump(
                                                &buf,
                                                "%d: %s",
                                                i,
                                                ShowType(v__(t0->types, i))
                                        );
                                } else {
                                        dump(
                                                &buf,
                                                "%s%s:%s %s",
                                                TERM(38;2;240;158;58),
                                                v__(t0->names, i),
                                                TERM(0),
                                                ShowType(v__(t0->types, i))
                                        );
                                }
                        }
                        if (t0->repeat != NULL) {
                                if (vN(t0->types) > 0) {
                                        dump(&buf, ", ");
                                }
                                dump(&buf, "%s...%s%s", TERM(93), ShowType(t0->repeat), TERM(0));
                        }
                        dump(&buf, "%s}%s", TERM(38:2:240:158:58), TERM(0));
                } else {
                        dump(&buf, "%s(%s", TERM(38:2:240:158:58), TERM(0));
                        for (int i = 0; i < vN(t0->types); ++i) {
                                dump(
                                        &buf,
                                        (i == 0) ? "%s" : ", %s",
                                        ShowType(v__(t0->types, i))
                                );
                        }
                        if (t0->repeat != NULL) {
                                if (vN(t0->types) > 0) {
                                        dump(&buf, ", ");
                                }
                                dump(&buf, "%s...%s%s", TERM(93), ShowType(t0->repeat), TERM(0));
                        }
                        dump(&buf, "%s)%s", TERM(38:2:240:158:58), TERM(0));
                }
                break;

        case TYPE_VARIABLE:
                dump(
                        &buf,
                        "%s",
                        IsTVar(t0)  ? TERM(38:2:255:153:187)
                      : IsFixed(t0) ? TERM(38:2:81:189:149)
                      : /*)  else (*/ TERM(91;1)
                );
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
                        dump(&buf, "%s{%d}%s", (t0->level >= CurrentLevel) ? TERM(94) : TERM(96), t0->level, TERM(0));
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

        return vN(buf) == 0 ? S2("<?>") : buf.items;
}

Type *
type_unfixed(Ty *ty, Type *t0)
{
        xDDD();

        if (IsBottom(t0)) {
                return BOTTOM;
        }

        Type *t;

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
                if (t0->level < CurrentLevel) {
                        return t0;
                } else {
                        Type *t1 = LookEnv(ty, ty->tenv, t0->id);
                        return (t1 != NULL) ? t1 : (variance ? TYPE_ANY : UNKNOWN);
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
                        t0->concrete &= IsConcrete(v__(t0->types, i));
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
                        t0->concrete &= IsConcrete(v__(t0->types, i));
                }
                break;

        case TYPE_TUPLE:
                if (t0->repeat != NULL) {
                        t0->repeat = MakeConcrete_(ty, t0->repeat, refs, variance);
                        t0->concrete &= t0->repeat->concrete;
                }
        case TYPE_SEQUENCE:
        case TYPE_LIST:
                CloneVec(t0->types);
                for (int i = 0; i < vN(t0->types); ++i) {
                        *v_(t0->types, i) = MakeConcrete_(ty, v__(t0->types, i), refs, variance);
                        t0->concrete &= IsConcrete(v__(t0->types, i));
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
                        t0->concrete &= IsConcrete(v__(t0->args, i));
                }
                break;

        case TYPE_CLASS:
        case TYPE_TAG:
                break;

        case TYPE_FUNCTION:
                CloneVec(t0->params);
                CloneVec(t0->constraints);
                for (int i = 0; i < vN(t0->params); ++i) {
                        Param *p = v_(t0->params, i);
                        p->type = MakeConcrete_(ty, p->type, refs, !variance);
                        t0->concrete &= IsConcrete(p->type);
                }
                for (int i = 0; i < vN(t0->constraints); ++i) {
                        Constraint *c = v_(t0->constraints, i);
                        c->t0 = MakeConcrete_(ty, c->t0, refs, variance);
                        c->t1 = MakeConcrete_(ty, c->t1, refs, variance);
                        c->t2 = MakeConcrete_(ty, c->t2, refs, variance);
                }
                t0->rt = MakeConcrete_(ty, t0->rt, refs, variance);
                t0->concrete &= IsConcrete(t0->rt);
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
                if (m == NULL) {
                        m = FindGetter(t0->class, name);
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

inline static Type *
CloneOverload(Ty *ty, Type *t0)
{
        Type *t1 = CloneType(ty, t0);

        if (TypeType(t1) == TYPE_INTERSECT) {
                CloneVec(t1->types);
        }

        return t1;
}

Type *
type_op(Ty *ty, Expr const *e)
{
        Type *t0 = op_type(e->op.b);
        Type *v0 = NewVar(ty);
        Type *u0 = NewRecord(
                e->op.id,
                NewFunction(v0)
        );
        return type_both(
                ty,
                t0,
                NewFunction(u0, v0)
        );
}

Type *
type_binary_op(Ty *ty, Expr const *e)
{
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
                return UNKNOWN;
        }

        Type *t0 = Reduce(ty, Relax(e->left->_type));
        Type *t1 = Reduce(ty, Relax(e->right->_type));
        Type *t2 = NewVar(ty);

        Type *op0 = CloneType(ty, op_type(op));

        if (TypeType(op0) == TYPE_INTERSECT) {
                CloneVec(op0->types);
        }

        if (TrySolve2Op(ty, op, op0, t0, t1, t2) == NULL) {
                xvP(
                        ToSolve,
                        CONSTRAINT(
                                .type = TC_2OP,
                                .t0  = t0,
                                .t1  = t1,
                                .t2  = t2,
                                .op0 = op0,
                                .op  = op,
                                .src = e
                        )
                );
        }

        XXTLOG("binary_op(%s): %s", intern_entry(&xD.b_ops, op)->name, ShowType(t2));
        XXTLOG("  %s", ShowType(t0));
        XXTLOG("  %s", ShowType(t1));

        return t2;
}

Type *
type_unary_hash_t(Ty *ty, Type const *t0)
{
        xDDD();

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
        return NULL;
}

Type *
type_wtf(Ty *ty, Expr const *e)
{
        xDDD();

        Type *t0 = NewVar(ty);

        Unify(ty, Either(ty, t0, NIL_TYPE), e->left->_type, true);
        Unify(ty, t0, e->right->_type, true);

        return t0;
}

Type *
type_either(Ty *ty, Type *t0, Type *t1)
{
        return (t0 == NULL) ? t1 : Either(ty, t0, t1);
}

Type *
type_both(Ty *ty, Type *t0, Type *t1)
{
        xDDD();

        if (IsBottom(t0)) {
                return t1;
        }

        if (
                TypeType(t0) == TYPE_INTERSECT
             && TypeType(t1) == TYPE_INTERSECT
        ) {
                avPv(t0->types, t1->types);
        } else if (t0->type == TYPE_INTERSECT) {
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
type_iterable_type(Ty *ty, Type *t0, int n)
{
        xDDD();

        Type *t1;
        Type *t2;

        Type *u0;
        Type *u1;
        Type *u2;

        switch (n) {
        case 0:
                return UNKNOWN;

        case 1:
                t1 = NewVar(ty);
                t2 = NewObject(CLASS_ITERABLE, t1);
                break;

        case 2:
                u0 = NewVar(ty);
                u1 = NewVar(ty);
                t1 = NewList(u0, u1);
                t2 = NewObject(CLASS_ITERABLE, u0, u1);
                break;

        default:
                u0 = NewVar(ty);
                u1 = NewVar(ty);
                u2 = NewVar(ty);
                t1 = NewList(u0, u1, u2);
                t2 = NewObject(CLASS_ITERABLE, u0, u1, u2);
                break;
        }

        Unify(ty, t2, t0, true);

        if (n > 1) {
                avP(t1->types, TYPE_INT);
                while (vN(t1->types) < n) {
                        avP(t1->types, UNKNOWN);
                }
        }

        TLOG("iterable_type(%d):", n);
        TLOG("  %s", ShowType(t0));
        TLOG("  %s", ShowType(t1));

        return t1;
}

Type *
type_special_str(Ty *ty, Expr const *e)
{
        xDDD();

        if (e->lang == NULL) {
                return TYPE_STRING;
        }

        Type *a0 = NewVar(ty);
        Type *t0 = NewVar(ty);
        Type *u0 = NewTuple(
                a0,
                Either(ty, TYPE_STRING, NIL_TYPE),
                Either(ty, TYPE_INT, NIL_TYPE)
        );
        Type *f0 = NewFunction(
                NewArray(
                        Either(
                                ty,
                                TYPE_STRING,
                                u0
                        )
                ),
                t0
        );

        for (int i = 0; i < vN(e->expressions); ++i) {
                Unify(ty, a0, v__(e->expressions, i)->_type, true);
        }

        Unify(ty, f0, e->lang->_type, true);

        return t0;
}

Type *
type_not_nil(Ty *ty, Type *t0)
{
        xDDD();

        Type *u0 = NewVar(ty);

        UnifyX(ty, Either(ty, u0, NIL_TYPE), t0, true, true);

        return u0;
}

Type *
type_without(Ty *ty, Type *t0, Type *t1)
{
        xDDD();

        Type *u0 = NewVar(ty);

        UnifyX(ty, Either(ty, u0, t1), t0, true, false);

        return u0;
}

static Type *
BoundedBy(Ty *ty, Type *t0, Type *t1)
{
        xDDD();

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
        xDDD();

        Type *t1 = NewObject(class);
        Type *t2 = BoundedBy(ty, t0, t1);

        if (t2 != NULL) {
                return t2;
        }

        if (TagOf(t1) != -1) {
                avP(t1->args, NewVar(ty));
                return t1;
        }

        for (int i = 0; i < vN(t1->class->type->bound); ++i) {
                avP(t1->args, NewVar(ty));
        }

        return t1;
}

void
type_scope_push(Ty *ty, Expr *fun)
{
        xDDDDD();
        xvP(FunStack, fun);
        EnterScope();
}

void
type_scope_pop(Ty *ty)
{
        xDDDDD();
        LeaveScope();
        vvX(FunStack);
}

static void
fixup(Ty *ty, Type *t0)
{
        Type *g0 = Generalize(ty, t0);
        XXTLOG("  g0:  %s", ShowType(g0));

        TypeEnv *env = ty->tenv;
        ty->tenv = NewEnv(ty, NULL);

        U32Vector bound = g0->bound;
        v00(g0->bound);

        for (int i = 0; i < vN(bound); ++i) {
                u32 id = v__(bound, i);
                int nref = CountRefs(g0, id);
                if (ContainsID(&FixedTypeVars, id)) {
                        avP(g0->bound, id);
                } else if (nref > 1) {
                        Type *var0 = NewTVar(ty);
                        PutEnv(ty, ty->tenv, id, var0);
                        avP(g0->bound, var0->id);
                } else {
                        XXTLOG("  drop %s, only %d refs in %s", VarName(ty, id), nref, ShowType(g0));
                }
        }

        g0 = MakeConcrete(ty, g0, NULL);
        XXTLOG("  g0:  %s", ShowType(g0));

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
        xDDDDD();

        Type *t0 = e->_type;

        if (TypeType(t0) != TYPE_FUNCTION) {
                return;
        }

        if (e->class > -1) {
                XXTLOG("fixup(%s.%s)[%d]:", class_name(ty, e->class), e->name, CurrentLevel);
                XXTLOG("    %s", ShowType(t0));
        } else {
                XXTLOG("fixup(%s)[%d]:", e->name ? e->name : "", CurrentLevel);
                XXTLOG("    %s", ShowType(t0));
        }

        fixup(ty, t0);

        if (vN(e->type_bounds) > 0) {
                ty->tenv = ty->tenv->parent;
        }
}

static Type *
TupleSubscriptType(Ty *ty, Type const *t0)
{
        Type *t1 = NewType(ty, TYPE_INTERSECT);
        Type *t2 = NewType(ty, TYPE_UNION);

        t1->fixed = true;
        t2->fixed = true;

        for (int i = 0; i < vN(t0->types); ++i) {
                avP(
                        t1->types,
                        NewFunction(
                                type_integer(ty, i),
                                v__(t0->types, i)
                        )
                );
                avP(t2->types, v__(t0->types, i));
        }

        if (t0->repeat != NULL) {
                avP(t2->types, t0->repeat);
        }

        avP(
                t1->types,
                NewFunction(
                        TYPE_INT,
                        Reduce(ty, t2)
                )
        );

        return t1;
}

Type **
FindRecordEntry(Type const *t0, int i, char const *name)
{
        if (TypeType(t0) != TYPE_TUPLE) {
                return NULL;
        }

        if (name == NULL) {
                return (i < vN(t0->types))
                     ? v_(t0->types, i)
                     : (Type **)&t0->repeat;
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
                CloneVec((*t0)->required);

                for (int i = 0; i < vN(t1->types); ++i) {
                        char const *name = v__(t1->names, i);
                        Type *e1 = v__(t1->types, i);
                        Type **e2 = FindRecordEntry(*t0, i, name);
                        if (e2 == NULL) {
                                AddEntry(*t0, e1, name, false);
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
        TLOG("TypeCheck():");
        TLOG("    %s", VSC(v));
        TLOG("    %s", ShowType(t0));

        t0 = Resolve(ty, t0);

        if (IsBottom(t0)) {
                return true;
        }

        if (v->type == VALUE_NIL) {
                return (TypeType(t0) == TYPE_VARIABLE)
                    || type_check_x(ty, t0, NIL_TYPE, false);
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
        case TYPE_ALIAS:
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
        CurrentLevel = 0;
        v0(WorkIndex);
        v0(ToSolve);
        v0(FunStack);
        EnterScope();
}

void
type_completions(Ty *ty, Type const *t0, char const *pre, ValueVector *out)
{
        expression_vector exprs = {0};
        int_vector depths = {0};

        int prefix_len = (pre == NULL) ? 0 : strlen(pre);

        switch (TypeType(t0)) {
        case TYPE_OBJECT:
                class_completions(ty, StrictClassOf(t0), pre, &exprs, &depths);
                for (int i = 0; i < vN(exprs); ++i) {
                        Expr const *e = v__(exprs, i);
                        switch (e->type) {
                        case EXPRESSION_FUNCTION:
                        case EXPRESSION_MULTI_FUNCTION:
                                xvP(
                                        *out,
                                        vTn(
                                                "name", xSz(e->name),
                                                "doc",  (e->doc == NULL) ? NIL : xSz(e->doc),
                                                "type", xSz(ShowType(SolveMemberAccess(ty, (Type *)t0, e->_type))),
                                                "kind", (e->mtype == MT_GET) ? INTEGER(10) : INTEGER(2),
                                                "depth", INTEGER(v__(depths, i))
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
                                                "kind",  INTEGER(5),
                                                "depth", INTEGER(v__(depths, i))
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
                                                "kind",  INTEGER(5),
                                                "depth", INTEGER(v__(depths, i))
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
                                        "kind", INTEGER(5),
                                        "depth", INTEGER(0)
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
                return class_get(ty, v->class);
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
        xDDD();

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

        case TyRegexVT:
                return TYPE_REGEXV;

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
                return class_get(ty, v->class)->object_type;
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
                        Type *u0 = type_from_ty(ty, &inner.items[i]);
                        if (inner.ids[i] == -1) {
                                AddEntry(t0, u0);
                        } else {
                                AddEntry(t0, u0, M_NAME(inner.ids[i]));
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

i32
type_approx_class(Type const *t0)
{
        return StrictClassOf(t0);
}

void
type_reset(Ty *ty)
{
        ToSolve.count = (vN(WorkIndex) > 0)
                      ? *vvL(WorkIndex)
                      : 0;
}

void
type_reset_names(Ty *ty)
{
        itable_clear(&VarNameTable);
        itable_copy(ty, &VarNameTable, &FixedVarNameTable);
        VarLetter = 'a';
        VarNumber = 0;
}

bool
type_iter(Ty *ty)
{
        bool any = false;

        if (ENABLED) {
                while (TryProgress(ty)) {
                        any = true;
                }
        }

        if (!any && vN(ToSolve) > 0) {
                type_reset(ty);
        }

        return any;
}

/* vim: set sts=8 sw=8 expandtab: */
