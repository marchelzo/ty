typedef struct {
        i32 const *ids;
        i32        index;
} RecordCache;

static Value *
record_slot(Value *value, i32 member, RecordCache *cache)
{
        if (value->type != VALUE_TUPLE || value->ids == NULL) {
                return NULL;
        }

        for (i32 i = 0; i < value->count; ++i) {
                if (value->ids[i] == member) {
                        cache->ids   = value->ids;
                        cache->index = i;
                        return &value->items[i];
                }
        }

        return NULL;
}

static void
record_path(
        BcLir *c,
        LirReg value,
        i32 member,
        LirReg slot,
        LirLabel other,
        LirLabel have,
        LirLabel slow
)
{
        RecordCache *cache = alloc0(sizeof *cache);
        LirLabel     miss  = newlabel(c);

        expect(c, value, 0, VALUE_TUPLE, other);

        LirReg ids    = ldp(c, value, VOFF(ids));
        LirReg cached = pval(c, cache);
        LirReg seen   = ldp(c, cached, offsetof(RecordCache, ids));

        jcc(c, LIR_NE, lir_r(ids), lir_r(seen), miss);

        LirReg index = ldw(c, cached, offsetof(RecordCache, index));
        LirReg items = ldp(c, value, VOFF(items));
        LirReg shift = binop(c, LIR_SHL, LIR_I64, lir_r(index), lir_i(5));

        vset(c, LIR_LEA, slot, lir_m(items, shift, 1, 0));
        jump(c, have);

        bind(c, miss);

        LirReg found = ccallf(
                c,
                record_slot,
                LT_PTR,
                CF_PURE,
                preg(value),
                imm32(member),
                preg(cached)
        );

        mov(c, slot, found);
        jz(c, slot, slow);
        jump(c, have);
}

static Class *
hint_class(BcLir *c, i32 offset)
{
        Expr const *expr = expr_of(c->function);

        if (expr == NULL) {
                return NULL;
        }

        T2Type type = find_type_hint(&expr->type_hints, offset);

        return (type == T2_TYPE_INVALID) ? NULL : expected_class_of(c->ctx, type);
}

static LirReg
known_field_slot(
        BcLir *c,
        LirReg value,
        Class *class,
        i32 member,
        bool writing,
        LirLabel slow
)
{
        if (class == NULL || class->i < CLASS_PRIMITIVE) {
                return LIR_NONE;
        }

        u16 field = offset_of(class, member, writing, OFF_FIELD);

        if (field == OFF_NOT_FOUND) {
                return LIR_NONE;
        }

        guard_class(c, value, class->i, slow);

        LirReg object = ldp(c, value, VOFF(object));

        return addr(c, object, offsetof(TyObject, slots) + vat(field & OFF_MASK));
}

static LirReg
field_slot(BcLir *c, LirReg value, i32 member, bool writing, LirLabel slow)
{
#define OFFSETS(f) (writing ? offsetof(Class, offsets_w.f) : offsetof(Class, offsets_r.f))
        i32 count = OFFSETS(count);
        i32 items = OFFSETS(items);
#undef OFFSETS

        expect(c, value, 0, VALUE_OBJECT, slow);

        LirReg object   = ldp(c, value, VOFF(object));
        LirReg class    = ldp(c, object, offsetof(TyObject, class));
        LirReg actual   = ldw(c, value, VOFF(class));
        LirReg declared = ldw(c, class, offsetof(Class, i));

        jcc(c, LIR_NE, lir_r(actual), lir_r(declared), slow);
        jcc(c, LIR_UGE, lir_i(member), lir_r(ldq(c, class, count)), slow);

        LirReg offsets = ldp(c, class, items);
        LirReg field   = ldx(c, LIR_LD_U16, LIR_I64, offsets, member * sizeof (u16));
        LirReg kind    = binop(c, LIR_SHR, LIR_I64, lir_r(field), lir_i(OFF_SHIFT));

        unless(c, kind, OFF_FIELD, slow);
        field = binop(c, LIR_AND, LIR_I64, lir_r(field), lir_i(OFF_MASK));

        return elem(c, object, field, offsetof(TyObject, slots));
}

static LirReg
any_field_slot(
        BcLir *c,
        LirReg value,
        Class *class,
        i32 member,
        bool writing,
        LirLabel slow
)
{
        LirReg known = known_field_slot(c, value, class, member, writing, slow);

        if (known != LIR_NONE) {
                return known;
        }

        if (class != NULL && class->i >= CLASS_PRIMITIVE) {
                return field_slot(c, value, member, writing, slow);
        }

        LirReg   slot  = lir_reg(c->L, LIR_PTR);
        LirLabel other = newlabel(c);
        LirLabel have  = newlabel(c);

        record_path(c, value, member, slot, other, have, slow);

        bind(c, other);

        LirReg field = field_slot(c, value, member, writing, slow);

        mov(c, slot, field);

        bind(c, have);

        return slot;
}

static i32
value_type_of(Class const *class)
{
        switch (class->i) {
        case CLASS_INT:   return VALUE_INTEGER;
        case CLASS_FLOAT: return VALUE_REAL;
        case CLASS_BOOL:  return VALUE_BOOLEAN;
        default:          return (class->i >= CLASS_PRIMITIVE) ? VALUE_OBJECT : -1;
        }
}

static void
guard_receiver(BcLir *c, LirReg value, Class *class, LirLabel miss)
{
        i32 type = value_type_of(class);

        if (type == VALUE_OBJECT) {
                guard_class(c, value, class->i, miss);
        } else {
                expect(c, value, 0, type, miss);
        }

        guard_epoch(c, miss);
}

static bool
known_getter(
        BcLir *c,
        LirReg value,
        Class *class,
        i32 member,
        i32 out,
        LirLabel slow,
        LirLabel done
)
{
        if (class == NULL || value_type_of(class) < 0) {
                return false;
        }

        u16 off = offset_of(class, member, false, OFF_GETTER);

        if (off == OFF_NOT_FOUND || (off & OFF_MASK) >= vN(class->getters.values)) {
                return false;
        }

        Value const *getter = v_(class->getters.values, off & OFF_MASK);

        if (!roomy(getter, 0) || param_count_of(getter) != 0) {
                return false;
        }

        guard_receiver(c, value, class, slow);
        try_plan(c, getter, TY_INLINE_METHOD, 0, out, value, class, NULL, out, done);
        inline_call(c, konst(c, getter), getter, out, 0, value, slow, done);

        return true;
}

static bool
from_prelude(Value const *fn)
{
        return (fn != NULL)
            && (fn->type == VALUE_FUNCTION)
            && !from_eval(fn)
            && (expr_of(fn)->mod != NULL)
            && s_eq(expr_of(fn)->mod->name, "prelude");
}

static void
abs_in_place(BcLir *c, LirReg value, bool real)
{
        if (real) {
                LirReg bits = ldq(c, value, VOFF(z));
                LirReg mag  = binop(c, LIR_AND, LIR_I64, lir_r(bits), lir_i(INT64_MAX));
                stq(c, value, VOFF(z), lir_r(mag));
                return;
        }

        LirLabel positive = newlabel(c);
        LirReg   z        = ldq(c, value, VOFF(z));

        jcc(c, LIR_GE, lir_r(z), lir_i(0), positive);
        stq(c, value, VOFF(z), lir_r(unop(c, LIR_NEG, LIR_I64, lir_r(z))));

        bind(c, positive);
}

static bool
numeric_getter(
        BcLir *c,
        LirReg value,
        Class *class,
        i32 member,
        LirLabel slow,
        LirLabel done
)
{
        if (class == NULL || (class->i != CLASS_FLOAT && class->i != CLASS_INT)) {
                return false;
        }

        char const *name = M_NAME(member);
        bool        real = (class->i == CLASS_FLOAT);
        bool        sqrt = s_eq(name, "sqrt");
        bool        abs  = s_eq(name, "abs");
        bool        flt  = s_eq(name, "float") && !real;

        if (!sqrt && !abs && !flt) {
                return false;
        }

        if (!from_prelude(class_lookup_getter_i(c->ctx, class->i, member))) {
                return false;
        }

        expect(c, value, 0, real ? VALUE_REAL : VALUE_INTEGER, slow);

        if (abs) {
                abs_in_place(c, value, real);
        } else {
                LirReg x = real
                         ? ldf(c, value, VOFF(real))
                         : unop(c, LIR_I2F, LIR_F64, lir_r(ldq(c, value, VOFF(z))));
                x = sqrt ? unop(c, LIR_FSQRT, LIR_F64, lir_r(x)) : x;
                put_real(c, value, 0, x);
        }

        jump(c, done);

        return true;
}

static void
fast_member(
        BcLir *c,
        LirReg value,
        LirReg out,
        i32 member,
        bool self,
        LirLabel slow,
        LirLabel done
)
{
        Class *class = self ? self_class(c) : hint_class(c, c->at);

        if (!self && numeric_getter(c, value, class, member, slow, done)) {
                return;
        }

        LirReg slot = known_field_slot(c, value, class, member, false, slow);

        if (slot == LIR_NONE) {
                if (known_getter(c, value, class, member, c->sp - !self, slow, done)) {
                        return;
                }
                slot = any_field_slot(c, value, class, member, false, slow);
        }

        copy(c, out, 0, slot, 0);

#ifdef TY_PROFILER
        xinc(c, &jit_stats.member_fast);
#endif

        jump(c, done);
}

static void
lower_member(BcLir *c, i32 member, bool self)
{
        LirLabel slow  = newlabel(c);
        LirLabel done  = newlabel(c);
        LirReg   out   = slot_of(c, c->sp - !self);
        bool     known = self && (c->self_index >= 0);
        LirReg   value = known ? addr(c, c->locals, vat(c->self_index)) : out;

        if ((!self && !c->compact) || known) {
                fast_member(c, value, out, member, self, slow, done);
        }

        bind(c, slow);
        tycall(
                c,
                jit_rt_member,
                LT_VOID,
                preg(out),
                { LT_PTR, self ? lir_i(0) : lir_r(out) },
                imm32(member)
        );

        bind(c, done);
        c->sp += self;
}
