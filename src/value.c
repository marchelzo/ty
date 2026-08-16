#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <inttypes.h>
#ifdef TY_BOX_STATS
#include <stdatomic.h>
#endif

#include <pcre2.h>
#include <xxhash.h>

#include "ty.h"
#include "dtoa.h"
#include "value.h"
#include "xd.h"
#include "dict.h"
#include "blob.h"
#include "queue.h"
#include "tags.h"
#include "class.h"
#include "gc.h"
#include "vm.h"
#include "ast.h"
#include "compiler.h"
#include "functions.h"
#include "types.h"
#include "highlight.h"

static _Thread_local vec(Dict *) show_dicts;
static _Thread_local vec(Value *) show_tuples;
static _Thread_local vec(Array *) show_arrays;
static _Thread_local vec(Queue *) show_queues;

static void
append_decimal_integer(Ty *ty, byte_vector *buf, imax value)
{
        char storage[sizeof(value) * 3 + 2];
        char *p = storage + sizeof storage;
        bool negative = value < 0;
        umax magnitude = negative
                       ? (umax)(-(value + 1)) + 1
                       : (umax)value;

        do {
                *--p = '0' + magnitude % 10;
                magnitude /= 10;
        } while (magnitude != 0);

        if (negative) *--p = '-';
        svPn(*buf, p, storage + sizeof storage - p);
}

#ifdef TY_BOX_STATS
static _Atomic uint64_t box_counts[VALUE_ANY + 1];
static atomic_flag box_stats_registered = ATOMIC_FLAG_INIT;
static _Atomic uint64_t string_clone_count;
static _Atomic uint64_t string_wrap_count;
static _Atomic uint64_t string_view_count;

static char const *
box_type_name(int type)
{
        switch (type) {
        case VALUE_FUNCTION:         return "Function";
        case VALUE_BOUND_FUNCTION:   return "BoundFunction";
        case VALUE_STAR_FUNCTION:    return "StarFunction";
        case VALUE_METHOD:           return "Method";
        case VALUE_BUILTIN_FUNCTION: return "BuiltinFunction";
        case VALUE_BUILTIN_METHOD:   return "BuiltinMethod";
        case VALUE_FOREIGN_FUNCTION: return "ForeignFunction";
        case VALUE_NATIVE_FUNCTION:  return "NativeFunction";
        case VALUE_GENERATOR_0:      return "Generator0";
        case VALUE_TAG:              return "Tag";
        case VALUE_OPERATOR:         return "Operator";
        case VALUE_TYPE:             return "Type";
        case VALUE_INTEGER:          return "LargeInteger";
        case VALUE_STRING:           return "DecoratedString";
        case VALUE_SENTINEL:         return "Sentinel";
        case VALUE_INDEX:            return "Index";
        case VALUE_NAMESPACE:        return "Namespace";
        case VALUE_MODULE:           return "Module";
        case VALUE_PTR:              return "Ptr";
        case VALUE_REF:              return "Ref";
        case VALUE_TUPLE:            return "Tuple";
        case VALUE_TRACE:            return "Trace";
        case VALUE_FUN_META:         return "FunMeta";
        default:                     return "Other";
        }
}

static void
dump_box_stats(void)
{
        uint64_t total = 0;
        for (int type = 0; type <= VALUE_ANY; ++type) {
                uint64_t n = atomic_load_explicit(&box_counts[type], memory_order_relaxed);
                if (n != 0) {
                        fprintf(stderr, "VALUE_BOX %2d %-18s %" PRIu64 "\n", type, box_type_name(type), n);
                        total += n;
                }
        }
        fprintf(stderr, "VALUE_BOX -- %-18s %" PRIu64 "\n", "TOTAL", total);
        fprintf(stderr, "VALUE_STRING clone              %" PRIu64 "\n",
                atomic_load_explicit(&string_clone_count, memory_order_relaxed));
        fprintf(stderr, "VALUE_STRING wrap               %" PRIu64 "\n",
                atomic_load_explicit(&string_wrap_count, memory_order_relaxed));
        fprintf(stderr, "VALUE_STRING view               %" PRIu64 "\n",
                atomic_load_explicit(&string_view_count, memory_order_relaxed));
}
#endif

void
TyValueCleanup(void)
{
        xvF(show_dicts);
        xvF(show_tuples);
        xvF(show_arrays);
        xvF(show_queues);
}

Value
value_box(Ty *ty, ValuePayload payload)
{
#ifdef TY_BOX_STATS
        if (!atomic_flag_test_and_set_explicit(&box_stats_registered, memory_order_relaxed)) {
                atexit(dump_box_stats);
        }
        int type = payload.type & ~VALUE_TAGGED;
        if (type >= 0 && type <= VALUE_ANY) {
                atomic_fetch_add_explicit(&box_counts[type], 1, memory_order_relaxed);
        }
#endif
        /* Do not trigger a collection between evaluating the payload pointer(s) and
         * making the box visible as a Value/root.  Ordinary allocations still
         * perform the limit check; boxes use the registered unchecked path. */
        /* ValuePayload arrives by value and compound literals zero-initialize
         * every omitted member, so clearing the allocation a second time only
         * adds bandwidth to this hot exceptional path. */
        ValueBox *box = gc_alloc_object_unchecked(ty, sizeof *box, GC_VALUE_BOX);
        if (!TY_IS_READY) {
                /* Loader/compiler structures retain Values outside traced GC
                 * containers for the process lifetime. */
                NOGC(box);
        }
        box->payload = payload;
        return (Value){ .bits = nanbox_from_pointer(box) };
}

Value
value_integer(Ty *ty, imax z)
{
        if (z >= INT32_MIN && z <= INT32_MAX) {
                return (Value){ .bits = nanbox_from_int((int32_t)z) };
        }
        return value_box(ty, (ValuePayload){ .type = VALUE_INTEGER, .z = z });
}

Value
value_real(double real)
{
        return (Value){ .bits = nanbox_from_double(real) };
}

Value
value_boolean(bool boolean)
{
        return (Value){ .bits = nanbox_from_boolean(boolean) };
}

Value
value_string_clone_value(Ty *ty, void const *src, u32 n)
{
#ifdef TY_BOX_STATS
        atomic_fetch_add_explicit(&string_clone_count, 1, memory_order_relaxed);
#endif
        Value result = value_string_inline(ty, n);
        if (src != NULL && n != 0) memcpy((u8 *)V_STR(result), src, n);
        if (src == NULL) {
                V_STR(result) = NULL;
                V_STR0(result) = NULL;
        }
        return result;
}

Value
value_string_clone_nul_value(Ty *ty, void const *src, u32 n)
{
#ifdef TY_BOX_STATS
        atomic_fetch_add_explicit(&string_clone_count, 1, memory_order_relaxed);
#endif
        ValueBox *box = gc_alloc_object_unchecked(
                ty, sizeof *box + n + 1, GC_VALUE_BOX
        );
        u8 *bytes = (u8 *)(box + 1);
        box->payload = (ValuePayload) {
                .type=VALUE_STRING,
                .str=src != NULL ? bytes : NULL,
                .bytes=n,
                .str0=src != NULL ? bytes : NULL,
                .inline_bytes=true
        };
        if (src != NULL) {
                if (n != 0) memcpy(bytes, src, n);
                bytes[n] = '\0';
        }
        return (Value){ .bits = nanbox_from_pointer(box) };
}

Value
value_string_inline(Ty *ty, u32 n)
{
        ValueBox *box = gc_alloc_object_unchecked(
                ty, sizeof *box + n, GC_VALUE_BOX
        );
        u8 *bytes = (u8 *)(box + 1);
        box->payload = (ValuePayload) {
                .type=VALUE_STRING,
                .str=bytes,
                .bytes=n,
                .str0=bytes,
                .inline_bytes=true
        };
        return (Value){ .bits = nanbox_from_pointer(box) };
}

Value
value_string_wrap(Ty *ty, void const *src, u32 n, bool ro)
{
#ifdef TY_BOX_STATS
        atomic_fetch_add_explicit(&string_wrap_count, 1, memory_order_relaxed);
#endif
        return value_box(ty, (ValuePayload){
                .type=VALUE_STRING, .str=src, .bytes=n, .str0=(u8 *)src, .ro=ro
        });
}

Value
value_string_view(Ty *ty, Value source, isize offset, u32 n)
{
#ifdef TY_BOX_STATS
        atomic_fetch_add_explicit(&string_view_count, 1, memory_order_relaxed);
#endif
        u8 const *str = V_STR(source) + offset;
        u8 *str0 = V_STR0(source);
        bool ro = V_RO(source);

        if (V_INLINE_BYTES(source)) {
                str0 = value_string_clone(ty, V_STR(source), V_BYTES(source));
                str = str0 + offset;
                ro = false;
        }

        return value_box(ty, (ValuePayload){
                .type=V_TYPE(source), .tags=V_TAGS(source), .src=V_SRC(source),
                .str=str, .bytes=n, .str0=str0, .ro=ro
        });
}

Value
value_tuple_wrap(Ty *ty, Value *items, i32 *ids, i32 count)
{
        /* items/ids may have just been allocated and are not yet reachable
         * from a Value, so publishing the descriptor must not trigger GC. */
        TupleValue *tuple = gc_alloc_object_unchecked(ty, sizeof *tuple, GC_TUPLE_VALUE);
        tuple->owner = NULL;
        tuple->items = items;
        tuple->ids = ids;
        tuple->count = count;
        tuple->src = 0;
        tuple->tags = 0;
        tuple->items_gc = items != NULL;
        tuple->ids_gc = ids != NULL;
        if (!TY_IS_READY) NOGC(tuple);
        return value_direct_tuple(tuple);
}

Value
value_tuple_alloc(Ty *ty, i32 count, bool with_ids)
{
        assert(count >= 0);
        usize items_bytes = (usize)count * sizeof (Value);
        usize ids_bytes = with_ids ? (usize)count * sizeof (i32) : 0;
        TupleValue *tuple = gc_alloc_object(
                ty, sizeof *tuple + items_bytes + ids_bytes, GC_TUPLE_VALUE);
        tuple->owner = NULL;
        tuple->items = (Value *)(tuple + 1);
        tuple->ids = with_ids ? (i32 *)((u8 *)tuple->items + items_bytes) : NULL;
        tuple->count = count;
        tuple->src = 0;
        tuple->tags = 0;
        tuple->items_gc = false;
        tuple->ids_gc = false;
        return value_direct_tuple(tuple);
}

void
value_tuple_nogc(Ty *ty, Value value)
{
        NOGC(value_direct_tuple_ptr(value));
}

void
value_tuple_okgc(Ty *ty, Value value)
{
        OKGC(value_direct_tuple_ptr(value));
}

Value
value_tuple_view(Ty *ty, Value source, i32 offset, i32 count)
{
        assert(value_is_direct_tuple(source));
        TupleValue *parent = value_direct_tuple_ptr(source);
        assert(offset >= 0 && count >= 0 && offset + count <= parent->count);
        TupleValue *tuple = gc_alloc_object_unchecked(ty, sizeof *tuple, GC_TUPLE_VALUE);
        tuple->owner = parent->owner != NULL ? parent->owner : parent;
        tuple->items = parent->items + offset;
        tuple->ids = parent->ids != NULL ? parent->ids + offset : NULL;
        tuple->count = count;
        tuple->src = parent->src;
        tuple->tags = parent->tags;
        tuple->items_gc = false;
        tuple->ids_gc = false;
        return value_direct_tuple(tuple);
}

Value
value_tuple_metadata(Ty *ty, Value source, u16 tags, u32 src)
{
        TupleValue *tuple = gc_alloc_object_unchecked(ty, sizeof *tuple, GC_TUPLE_VALUE);
        TupleValue *owner = value_direct_tuple_ptr(source);
        tuple->owner = owner->owner != NULL ? owner->owner : owner;
        tuple->items = owner->items;
        tuple->ids = owner->ids;
        tuple->count = owner->count;
        tuple->src = src;
        tuple->tags = tags;
        tuple->items_gc = false;
        tuple->ids_gc = false;
        return value_direct_tuple(tuple);
}

ValuePayload
value_payload(Value value)
{
        if (value_is_direct_array(value)) return (ValuePayload){ .type=VALUE_ARRAY, .array=value_direct_array_ptr(value) };
        if (value_is_direct_class(value)) return (ValuePayload){ .type=VALUE_CLASS, .class=value_direct_class_id(value) };
        if (value_is_direct_tag(value)) return (ValuePayload){ .type=VALUE_TAG, .tag=value_direct_tag_id(value) };
        if (value_is_direct_object(value)) return (ValuePayload){ .type=VALUE_OBJECT, .object=value_direct_object_ptr(value), .class=value_direct_object_ptr(value)->class->i };
        if (value_is_direct_tagged_int(value)) return (ValuePayload){ .type=VALUE_INTEGER | VALUE_TAGGED, .tags=value_direct_tagged_int_tags(value), .z=value_direct_tagged_int_value(value) };
        if (value_is_direct_tuple(value)) return (ValuePayload){ .type=V_TYPE(value), .tags=V_TAGS(value), .src=V_SRC(value), .count=V_COUNT(value), .items=V_ITEMS(value), .ids=V_IDS(value) };
        if (nanbox_is_pointer(value.bits)) return value_box_ptr(value)->payload;
        if (nanbox_is_int(value.bits)) return (ValuePayload){ .type=VALUE_INTEGER, .z=nanbox_to_int(value.bits) };
        if (nanbox_is_double(value.bits)) return (ValuePayload){ .type=VALUE_REAL, .real=nanbox_to_double(value.bits) };
        if (nanbox_is_boolean(value.bits)) return (ValuePayload){ .type=VALUE_BOOLEAN, .boolean=nanbox_to_boolean(value.bits) };
        if (nanbox_is_null(value.bits)) return (ValuePayload){ .type=VALUE_NIL };
        if (nanbox_is_undefined(value.bits)) return (ValuePayload){ .type=VALUE_NONE };
        assert(nanbox_is_empty(value.bits));
        return (ValuePayload){ .type=VALUE_ZERO };
}

static Value
value_inline_string_metadata(Ty *ty, Value value, u8 type, u16 tags, u32 src)
{
        /* Inline string bytes belong to their ValueBox.  A metadata-only box
         * cannot safely point into the old box because the old Value may no
         * longer be reachable. */
        Value result = value_string_clone_value(ty, V_STR(value), V_BYTES(value));
        ValuePayload *payload = &value_box_ptr(result)->payload;
        payload->type = type;
        payload->tags = tags;
        payload->src = src;
        return result;
}

Value
value_with_src(Ty *ty, Value value, u32 src)
{
        if (value_is_direct_tuple(value))
                return value_tuple_metadata(ty, value, V_TAGS(value), src);
        if ((V_TYPE(value) & ~VALUE_TAGGED) == VALUE_STRING && V_INLINE_BYTES(value))
                return value_inline_string_metadata(
                        ty, value, V_TYPE(value), V_TAGS(value), src);
        ValuePayload payload = value_payload(value);
        payload.src = src;
        return value_box(ty, payload);
}

Value
value_with_tags(Ty *ty, Value value, u16 tags)
{
        if (tags != 0 && nanbox_is_int(value.bits))
                return value_direct_tagged_int(nanbox_to_int(value.bits), tags);
        if (value_is_direct_tagged_int(value)) {
                if (tags != 0) return value_direct_tagged_int(value_direct_tagged_int_value(value), tags);
                return value_integer(ty, value_direct_tagged_int_value(value));
        }
        if (value_is_direct_tuple(value))
                return value_tuple_metadata(ty, value, tags, V_SRC(value));
        if ((V_TYPE(value) & ~VALUE_TAGGED) == VALUE_STRING && V_INLINE_BYTES(value)) {
                u8 type = tags ? VALUE_STRING | VALUE_TAGGED : VALUE_STRING;
                return value_inline_string_metadata(ty, value, type, tags, V_SRC(value));
        }
        ValuePayload payload = value_payload(value);
        payload.tags = tags;
        payload.type = tags ? (payload.type | VALUE_TAGGED) : (payload.type & ~VALUE_TAGGED);
        return value_box(ty, payload);
}

Value
value_with_type(Ty *ty, Value value, u8 type)
{
        if (value_is_direct_tuple(value) && (type & ~VALUE_TAGGED) == VALUE_TUPLE)
                return value_tuple_metadata(ty, value, V_TAGS(value), V_SRC(value));
        if ((V_TYPE(value) & ~VALUE_TAGGED) == VALUE_STRING
        && (type & ~VALUE_TAGGED) == VALUE_STRING
        && V_INLINE_BYTES(value))
                return value_inline_string_metadata(
                        ty, value, type, V_TAGS(value), V_SRC(value));
        ValuePayload payload = value_payload(value);
        payload.type = type;
        return value_box(ty, payload);
}

inline static void
MarkNext(Ty *ty, Value *v)
{
        xvP(ty->marking, v);
}

static bool
arrays_equal(Ty *ty, Value const *v1, Value const *v2)
{
        if (V_ARRAY(*(v1)) == V_ARRAY(*(v2))) {
                return true;
        }

        if (vN(*V_ARRAY(*v1)) != vN(*V_ARRAY(*v2))) {
                return false;
        }

        usize n = vN(*V_ARRAY(*v1));

        for (usize i = 0; i < n; ++i) {
                if (
                        !value_test_equality(
                                ty,
                                v_(*V_ARRAY(*v1), i),
                                v_(*V_ARRAY(*v2), i)
                        )
                )  {
                        return false;
                }
        }

        return true;
}

typedef struct {
        i32 id;
        Value val;
} RecordItem;

typedef vec(RecordItem) RecordItems;

static int
itemcmp(const void *a, const void *b)
{
        RecordItem const *x = a;
        RecordItem const *y = b;

        return (x->id < y->id) ? -1
             : (x->id > y->id) ?  1
             :                    0
             ;
}

static bool
records_equal(Ty *ty, Value const *v1, Value const *v2)
{
        RecordItems xs_named = {0};
        RecordItems ys_named = {0};

        ValueVector xs_unnamed = {0};
        ValueVector ys_unnamed = {0};

        SCRATCH_SAVE();

        for (usize i = 0; i < V_COUNT(*(v1)); ++i) {
                if (LIKELY(V_IDS(*v1)[i] != -1)) {
                        svP(xs_named, ((RecordItem) {
                                .id  = V_IDS(*v1)[i],
                                .val = V_ITEMS(*v1)[i]
                        }));
                } else {
                        svP(xs_unnamed, V_ITEMS(*v1)[i]);
                }
        }

        for (usize i = 0; i < V_COUNT(*(v2)); ++i) {
                if (LIKELY(V_IDS(*v2)[i] != -1)) {
                        svP(ys_named, ((RecordItem) {
                                .id  = V_IDS(*v2)[i],
                                .val = V_ITEMS(*v2)[i]
                        }));
                } else {
                        svP(ys_unnamed, V_ITEMS(*v2)[i]);
                }
        }

        if (
                (vN(xs_named) != vN(ys_named))
             || (vN(xs_unnamed) != vN(ys_unnamed))
        ) {
                SCRATCH_RESTORE();
                return false;
        }

        qsort(vv(xs_named), vN(xs_named), sizeof (RecordItem), itemcmp);
        qsort(vv(ys_named), vN(ys_named), sizeof (RecordItem), itemcmp);

        for (usize i = 0; i < vN(xs_named); ++i) {
                if (v_(xs_named, i)->id != v_(ys_named, i)->id) {
                        SCRATCH_RESTORE();
                        return false;
                }
                if (!v_eq(&v_(xs_named, i)->val, &v_(ys_named, i)->val)) {
                        SCRATCH_RESTORE();
                        return false;
                }
        }

        for (usize i = 0; i < vN(xs_unnamed); ++i) {
                if (!v_eq(v_(xs_unnamed, i), v_(ys_unnamed, i))) {
                        SCRATCH_RESTORE();
                        return false;
                }
        }

        SCRATCH_RESTORE();

        return true;
}

static int
compare_records(Ty *ty, Value const *v1, Value const *v2)
{
        RecordItems xs = {0};
        RecordItems ys = {0};

        SCRATCH_SAVE();

        for (usize i = 0; i < V_COUNT(*(v1)); ++i) {
                if (LIKELY(V_IDS(*v1)[i] != -1)) {
                        svP(xs, ((RecordItem) {
                                .id  = V_IDS(*v1)[i],
                                .val = V_ITEMS(*v1)[i]
                        }));
                } else {
                        svP(xs, ((RecordItem) {
                                .id  = -1,
                                .val = V_ITEMS(*v1)[i]
                        }));
                }
        }

        for (usize i = 0; i < V_COUNT(*(v2)); ++i) {
                if (LIKELY(V_IDS(*v2)[i] != -1)) {
                        svP(ys, ((RecordItem) {
                                .id  = V_IDS(*v2)[i],
                                .val = V_ITEMS(*v2)[i]
                        }));
                } else {
                        svP(ys, ((RecordItem) {
                                .id  = -1,
                                .val = V_ITEMS(*v2)[i]
                        }));
                }
        }

        qsort(vv(xs), vN(xs), sizeof (RecordItem), itemcmp);
        qsort(vv(ys), vN(ys), sizeof (RecordItem), itemcmp);

        for (usize i = 0; i < vN(xs); ++i) {
                if (v_(xs, i)->id != v_(ys, i)->id) {
                        SCRATCH_RESTORE();
                        return (v_(xs, i)->id < v_(ys, i)->id) ? -1 : 1;
                }
                int cmp = value_compare(ty, &v_(xs, i)->val, &v_(ys, i)->val);
                if (cmp != 0) {
                        SCRATCH_RESTORE();
                        return cmp;
                }
        }

        SCRATCH_RESTORE();

        return 0;
}

static bool
tuples_equal(Ty *ty, Value const *v1, Value const *v2)
{
        if (V_ITEMS(*(v1)) == V_ITEMS(*(v2)))
                return true;

        if (V_COUNT(*(v1)) != V_COUNT(*(v2)))
                return false;

        if (V_IDS(*(v1)) != NULL && V_IDS(*(v2)) != NULL) {
                return records_equal(ty, v1, v2);
        }

        usize n = V_COUNT(*(v1));

        for (usize i = 0; i < n; ++i) {
                if (
                        !value_test_equality(
                                ty,
                                &V_ITEMS(*(v1))[i],
                                &V_ITEMS(*(v2))[i]
                        )
                ) {
                        return false;
                }
        }

        return true;
}

inline static u64
str_hash(char const *str, u32 len)
{
        return XXH3_64bits(str, len);
}

inline static u64
hash64(u64 x)
{
        x ^= x >> 30;
        x *= 0xBF58476D1CE4E5B9ULL;
        x ^= x >> 27;
        x *= 0x94D049BB133111EBULL;
        x ^= x >> 31;
        return x;
}

inline static u64
ptr_hash(void const *p)
{
        return hash64((u64)(uptr)p);
}

inline static u64
flt_hash(double _x)
{
        u64 x;
        memcpy(&x, &_x, sizeof x);
        return hash64(x);
}

inline static u64
ary_hash(Ty *ty, Value const *a)
{
        u64 hash = 7234782527432842341ULL;

        for (usize i = 0; i < vN(*V_ARRAY(*a)); ++i) {
                u64 x = value_hash(ty, &V_ARRAY(*(a))->items[i]);
                hash = HashCombine(hash, x);
        }

        return hash;
}

inline static u64
queue_hash(Ty *ty, Value const *v)
{
        Queue *q = V_QUEUE(*(v));
        u64 h = 7234782527432842341ULL;
        usize n = _queue_count(q->head, q->tail, q->cap);

        for (usize i = 0; i < n; ++i) {
                u64 x = value_hash(ty, &q->items[(q->head + i) % q->cap]);
                h = HashCombine(h, x);
        }

        return h;
}

inline static u64
tpl_hash(Ty *ty, Value const *t)
{
        u64 hash = 1127573292757587281ULL;

        for (int i = 0; i < V_COUNT(*(t)); ++i) {
                u64 x = value_hash(ty, &V_ITEMS(*(t))[i]);
                hash = HashCombine(hash, x);
                if (V_IDS(*(t)) != NULL && V_IDS(*(t))[i] != -1) {
                        hash *= (V_IDS(*(t))[i] + 1);
                }
        }

        return hash;
}

inline static u64
obj_hash(Ty *ty, Value const *v)
{
        Value const *f = class_lookup_method_i(ty, V_CLASS(*(v)), NAMES._hash_);

        if (f != NULL) {
                Value hash = vm_call_method(ty, v, f, 0);
                if (V_TYPE(hash) != VALUE_INTEGER) {
                        zP(
                                "%s.__hash__() returned non-integer: %s",
                                class_name(ty, V_CLASS(*v)),
                                VSC(v)
                        );
                }
                return (u64)V_Z(hash);
        } else {
                return ptr_hash(V_OBJECT(*(v)));
        }
}

static u64
hash(Ty *ty, Value const *val)
{
        switch (V_TYPE(*(val)) & ~VALUE_TAGGED) {
        case VALUE_NIL:               return 0xDEADDEADDEADULL;
        case VALUE_BOOLEAN:           return V_BOOL(*(val)) ? 0xABCULL : 0xDEFULL;
        case VALUE_STRING:            return XXH3_64bits(ss(*val), sN(*val));
        case VALUE_INTEGER:           return hash64(V_Z(*(val)));
        case VALUE_REAL:              return flt_hash(V_REAL(*(val)));
        case VALUE_ARRAY:             return ary_hash(ty, val);
        case VALUE_QUEUE:             return queue_hash(ty, val);
        case VALUE_TUPLE:             return tpl_hash(ty, val);
        case VALUE_DICT:              return ptr_hash(V_DICT(*(val)));
        case VALUE_OBJECT:            return obj_hash(ty, val);
        case VALUE_METHOD:            return HashCombine(ptr_hash(V_METHOD(*val)), ptr_hash(V_THIS(*(val))));
        case VALUE_BUILTIN_METHOD:    return HashCombine(ptr_hash(V_BUILTIN_METHOD(*val)), ptr_hash(V_THIS(*(val))));
        case VALUE_BUILTIN_FUNCTION:  return ptr_hash(V_BUILTIN_FUNCTION(*(val)));
        case VALUE_BOUND_FUNCTION:
        case VALUE_FUNCTION:          return HashCombine(ptr_hash(V_INFO(*(val))), ptr_hash(V_ENV(*(val))));
        case VALUE_FOREIGN_FUNCTION:  return HashCombine(ptr_hash((void *)V_FF(*(val))), ptr_hash(V_FFI(*(val))));
        case VALUE_REGEX:             return ptr_hash(V_REGEX(*(val)));
        case VALUE_PTR:               return ptr_hash(V_PTR(*(val)));
        case VALUE_TAG:               return (((u64)V_TAG(*(val))) * 517929173925273293ULL);
        case VALUE_CLASS:             return (((u64)V_CLASS(*(val))) * 817364735284283413ULL);
        default:                      zP("attempt to hash invalid value: %s", VSC(val));
        }
}

u64
value_hash(Ty *ty, Value const *val)
{
        return ((u64)V_TAGS(*(val))) ^ hash(ty, val);
}

static char *
show_string(Ty *ty, u8 const *s, size_t n, bool use_color)
{
        byte_vector v = {0};
        i32 color = 0;

#define COLOR(i) do {                               \
        if (use_color && color != i) {              \
                svPn(v, TERM(i), strlen(TERM(i)));  \
                color = i;                          \
        }                                           \
} while (0)

        COLOR(92);

        svP(v, '\'');

        if (s != NULL) for (u8 const *c = s; c < s + n; ++c) switch (*c) {
        case '\t':
                COLOR(95);
                svP(v, '\\');
                svP(v, 't');
                break;

        case '\r':
                COLOR(95);
                svP(v, '\\');
                svP(v, 'r');
                break;

        case '\n':
                COLOR(95);
                svP(v, '\\');
                svP(v, 'n');
                break;

        case '\\':
                COLOR(95);
                svP(v, '\\');
                svP(v, '\\');
                break;

        case '\'':
                COLOR(95);
                svP(v, '\\');
                svP(v, '\'');
                break;

        case '\0':
                COLOR(91);
                svP(v, '\\');
                svP(v, '0');
                break;

        default:
                if (iscntrl(*c)) {
                        COLOR(93);
                        sxdf(&v, "\\x%02x", (u32)*c);

                } else {
                        COLOR(92);
                        svP(v, *c);
                }
                break;
        }

        COLOR(92);
        svP(v, '\'');

        COLOR(0);

#undef COLOR

        svP(v, '\0');

        return vv(v);
}

static noreturn void
uninit(Ty *ty, Symbol const *s)
{
        zP(
                "use of uninitialized variable %s%s%s%s (defined at %s%s%s:%s%d%s:%s%d%s)",
                TERM(1),
                TERM(93),
                s->identifier,
                TERM(0),
                TERM(34),
                s->mod->path,
                TERM(0),
                TERM(33),
                s->loc.line + 1,
                TERM(0),
                TERM(33),
                s->loc.col + 1,
                TERM(0)
        );
}

enum {
        SW_LIT     = 0x40,
        SW_POP_ARY,
        SW_POP_TPL,
        SW_POP_DCT,
        SW_POP_VIS,
        SW_POP_QUE,
};

#define WLIT(s) svP(work, VALUE_BOX_(.type=SW_LIT, .ptr=(void *)(s)))
#define WPOP(op) svP(work, VALUE_BOX_(.type=(op)))

static char *
show_impl(
        Ty *ty,
        Value const *root,
        u32 flags
)
{
        bool color = !(flags & TY_SHOW_NOCOLOR);

        byte_vector buf  = {0};
        ValueVector work = {0};

        svP(work, *root);

        while (vN(work) > 0) {
                Value v = vXx(work);

                switch (V_TYPE(v)) {
                case SW_LIT:
                {
                        char const *s = V_PTR(v);
                        svPn(buf, s, strlen(s));
                        continue;
                }
                case SW_POP_ARY: { vvX(show_arrays);   continue; }
                case SW_POP_TPL: { vvX(show_tuples);   continue; }
                case SW_POP_DCT: { vvX(show_dicts);    continue; }
                case SW_POP_VIS: { vvX(ty->visiting);  continue; }
                case SW_POP_QUE: { vvX(show_queues);   continue; }
                }

                if (
                        (V_TYPE(v) & VALUE_TAGGED)
                     && (V_TYPE(v) & ~VALUE_TAGGED) != VALUE_TUPLE
                ) {
                        WLIT(tags_close(ty, V_TAGS(v), color));
                        svP(work, stripped(ty, &v));
                        WLIT(tags_open(ty, V_TAGS(v), color));
                        continue;
                }

                switch (V_TYPE(v) & ~VALUE_TAGGED) {
                case VALUE_INTEGER:
                        if (color) {
                                sxdf(&buf, "%s%"PRIiMAX"%s", TERM(93), V_Z(v), TERM(0));
                        } else {
                                append_decimal_integer(ty, &buf, V_Z(v));
                        }
                        break;

                case VALUE_REAL:
                {
                        char *r = smA(512);
                        dtoa(V_REAL(v), r, 512);
                        if (color) {
                                sxdf(&buf, "%s%s%s", TERM(93), r, TERM(0));
                        } else {
                                sxdf(&buf, "%s", r);
                        }
                        break;
                }

                case VALUE_STRING:
                {
                        char *s = show_string(ty, ss(v), sN(v), color);
                        u32 len = strlen(s);
                        svPn(buf, s, len);
                        break;
                }

                case VALUE_BOOLEAN:
                {
                        char const *s = V_BOOL(v) ? "true" : "false";
                        if (color) {
                                sxdf(&buf, "%s%s%s", TERM(36), s, TERM(0));
                        } else {
                                sxdf(&buf, "%s", s);
                        }
                        break;
                }

                case VALUE_NIL:
                        if (color) {
                                sxdf(&buf, "%snil%s", TERM(95), TERM(0));
                        } else {
                                sxdf(&buf, "nil");
                        }
                        break;

                case VALUE_TYPE:
                {
                        char *s = type_show(ty, V_PTR(v));
                        svPn(buf, s, strlen(s));
                        break;
                }

                case VALUE_NAMESPACE:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<ns %s'%s'%s>%s",
                                        TERM(93),
                                        TERM(95),
                                        V_NAMESPACE(v)->name,
                                        TERM(93),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<ns '%s'>",
                                        V_NAMESPACE(v)->name
                                );
                        }
                        break;

                case VALUE_MODULE:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<module %s'%s'%s>%s",
                                        TERM(93),
                                        TERM(95),
                                        V_MOD(v)->name,
                                        TERM(93),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<module '%s'>",
                                        V_MOD(v)->name
                                );
                        }
                        break;

                case VALUE_ARRAY:
                {
                        for (int i = 0; i < vN(show_arrays); ++i) {
                                if (v__(show_arrays, i) == V_ARRAY(v)) {
                                        sxdf(&buf, "[...]");
                                        goto Next;
                                }
                        }

                        xvP(show_arrays, V_ARRAY(v));

                        int n = vN(*V_ARRAY(v));

                        WPOP(SW_POP_ARY);
                        WLIT("]");

                        for (int i = n - 1; i >= 0; --i) {
                                svP(work, *v_(*V_ARRAY(v), i));
                                if (i > 0) {
                                        WLIT(", ");
                                }
                        }

                        WLIT("[");

                        break;
                }

                case VALUE_TUPLE:
                {
                        for (int i = 0; i < vN(show_tuples); ++i) {
                                if (v__(show_tuples, i) == V_ITEMS(v)) {
                                        sxdf(&buf, "(...)");
                                        goto Next;
                                }
                        }

                        xvP(show_tuples, V_ITEMS(v));

                        bool tagged = (V_TYPE(v) & VALUE_TAGGED);

                        WPOP(SW_POP_TPL);

                        if (tagged) {
                                WLIT(tags_close(ty, V_TAGS(v), color));
                        } else {
                                WLIT(")");
                        }

                        for (int i = V_COUNT(v) - 1; i >= 0; --i) {
                                svP(work, V_ITEMS(v)[i]);
                                if (V_IDS(v) != NULL && V_IDS(v)[i] != -1) {
                                        char const *name = M_NAME(V_IDS(v)[i]);
                                        if (color) {
                                                WLIT(sfmt(
                                                        "%s%s%s: ",
                                                        TERM(34),
                                                        name,
                                                        TERM(0)
                                                ));
                                        } else {
                                                WLIT(sfmt(
                                                        "%s: ",
                                                        name
                                                ));
                                        }
                                }
                                if (i > 0) {
                                        WLIT(", ");
                                }
                        }

                        if (tagged) {
                                WLIT(tags_open(ty, V_TAGS(v), color));
                        } else {
                                WLIT("(");
                        }

                        break;
                }

                case VALUE_DICT:
                {
                        for (int i = 0; i < vN(show_dicts); ++i) {
                                if (v__(show_dicts, i) == V_DICT(v)) {
                                        sxdf(&buf, "{...}");
                                        goto Next;
                                }
                        }

                        xvP(show_dicts, V_DICT(v));

                        typedef struct { Value k, v; } KV;
                        vec(KV) items = {0};

                        dfor(V_DICT(v), {
                                svP(items, ((KV){
                                        *key,
                                        *val
                                }));
                        });

                        int n = vN(items);

                        WPOP(SW_POP_DCT);
                        WLIT(color ? sfmt("%s}%s", TERM(94;1), TERM(0)) : "}");

                        for (int i = n - 1; i >= 0; --i) {
                                KV kv = v__(items, i);
                                if (V_TYPE(kv.v) != VALUE_NIL) {
                                        svP(work, kv.v);
                                        WLIT(": ");
                                }
                                svP(work, kv.k);
                                if (i > 0) {
                                        WLIT(", ");
                                }
                        }

                        WLIT(color ? sfmt("%s%%{%s", TERM(94;1), TERM(0)) : "%{");

                        break;
                }

                case VALUE_REGEX:
                {
                        long bits = 0;
                        int  nf   = 0;
                        char flags[16] = {0};

                        pcre2_pattern_info(V_REGEX(v)->pcre2, PCRE2_INFO_ALLOPTIONS, &bits);

                        if (bits & PCRE2_MULTILINE) { flags[nf++] = 'm'; }
                        if (bits & PCRE2_DOTALL)    { flags[nf++] = 's'; }
                        if (bits & PCRE2_UTF)       { flags[nf++] = 'u'; }
                        if (bits & PCRE2_CASELESS)  { flags[nf++] = 'i'; }
                        if (bits & PCRE2_EXTENDED)  { flags[nf++] = 'x'; }
                        if (bits & PCRE2_ANCHORED)  { flags[nf++] = 'a'; }
                        if (bits & PCRE2_UNGREEDY)  { flags[nf++] = 'U'; }
                        if (bits & PCRE2_NEVER_UTF) { flags[nf++] = '7'; }
                        flags[nf] = '\0';

                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s/%s/%s%s%s",
                                        TERM(38;2;127;197;78),
                                        V_REGEX(v)->pattern,
                                        TERM(38;2;63;189;142),
                                        flags,
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "/%s/%s", V_REGEX(v)->pattern, flags);
                        }
                        break;
                }

                case VALUE_NATIVE_FUNCTION:
                case VALUE_FUNCTION:
                {
                        char const *cls  = class_name(ty, class_of(&v));
                        char const *name = name_of(&v);
                        char const *star = is_starred(&v) ? "*" : "";
                        char const *jit  = ((iptr)jit_of(&v) > 0xFA57)  ? " [jit]" : "";

                        if (color) {
                                if (class_of(&v) == -1) {
                                        sxdf(
                                                &buf,
                                                "%s<func %s%s%s%s%s%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                name,
                                                star,
                                                TERM(95),
                                                jit,
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "%s<func %s%s.%s%s%s%s%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                cls,
                                                name,
                                                star,
                                                TERM(95),
                                                jit,
                                                TERM(96),
                                                TERM(0)
                                        );
                                }
                        } else {
                                if (class_of(&v) == -1) {
                                        sxdf(&buf, "<func %s%s>", name, star);
                                } else {
                                        sxdf(&buf, "<func %s.%s%s>", cls, name, star);
                                }
                        }
                        break;
                }

                case VALUE_BOUND_FUNCTION:
                {
                        char const *cls  = class_name(ty, class_of(&v));
                        char const *name = name_of(&v);
                        char const *star = is_starred(&v) ? "*" : "";

                        if (color) {
                                Value self = self_of(&v);
                                WLIT(sfmt(
                                        "%s>%s",
                                        TERM(96),
                                        TERM(0)
                                ));
                                svP(work, self);
                                WLIT(sfmt(
                                        "%s<func %s%s.%s%s %sbound to %s",
                                        TERM(96),
                                        TERM(92),
                                        cls,
                                        name,
                                        star,
                                        TERM(96),
                                        TERM(0)
                                ));
                        } else {
                                if (class_of(&v) == -1) {
                                        sxdf(&buf, "<func %s%s>", name, star);
                                } else {
                                        sxdf(&buf, "<func %s.%s%s>", cls, name, star);
                                }
                        }
                        break;
                }

                case VALUE_METHOD:
                        if (V_THIS(v) == NULL) {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<method %s'%s'%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                name_of(V_METHOD(v)),
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<method '%s' at %p>",
                                                M_NAME(V_NAME(v)),
                                                (void *)V_METHOD(v)
                                        );
                                }
                        } else if (color) {
                                WLIT(sfmt(
                                        "%s>%s",
                                        TERM(96),
                                        TERM(0)
                                ));
                                svP(work, *V_THIS(v));
                                WLIT(sfmt(
                                        "%s<method %s'%s'%s bound to %s",
                                        TERM(96),
                                        TERM(92),
                                        name_of(V_METHOD(v)),
                                        TERM(96),
                                        TERM(0)
                                ));
                        } else {
                                WLIT(">");
                                svP(work, *V_THIS(v));
                                WLIT(sfmt(
                                        "<method '%s' bound to ",
                                        M_NAME(V_NAME(v))
                                ));
                        }
                        break;

                case VALUE_BUILTIN_METHOD:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<bound builtin method %s'%s'%s>%s",
                                        TERM(96),
                                        TERM(92),
                                        M_NAME(V_NAME(v)),
                                        TERM(96),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<bound builtin method '%s'>",
                                        M_NAME(V_NAME(v))
                                );
                        }
                        break;

                case VALUE_BUILTIN_FUNCTION:
                        if (V_NAME(v) == -1) {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<builtin>%s",
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(&buf, "<builtin>");
                                }
                        } else if (V_MODULE(v) == NULL) {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<builtin %s'%s'%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                M_NAME(V_NAME(v)),
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<builtin %s>",
                                                M_NAME(V_NAME(v))
                                        );
                                }
                        } else {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<builtin %s'%s::%s'%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                V_MODULE(v),
                                                M_NAME(V_NAME(v)),
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<builtin %s.%s>",
                                                V_MODULE(v),
                                                M_NAME(V_NAME(v))
                                        );
                                }
                        }
                        break;

                case VALUE_FOREIGN_FUNCTION:
                        if (V_XINFO(v) == NULL || V_XINFO(v)->name == NULL) {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<foreign function>%s",
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(&buf, "<foreign func>");
                                }
                        } else {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<foreign function %s'%s'%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                V_XINFO(v)->name,
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<foreign func %s>",
                                                V_XINFO(v)->name
                                        );
                                }
                        }
                        break;

                case VALUE_OPERATOR:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<%soperator %s%s%s>%s",
                                        TERM(96),
                                        TERM(92),
                                        TERM(94),
                                        M_NAME(V_UOP(v)),
                                        TERM(96),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<operator %s>",
                                        M_NAME(V_UOP(v))
                                );
                        }
                        break;

                case VALUE_CLASS:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<%sclass %s%s%s>%s",
                                        TERM(96),
                                        TERM(92),
                                        TERM(94),
                                        class_name(ty, V_CLASS(v)),
                                        TERM(96),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<class %s>",
                                        class_name(ty, V_CLASS(v))
                                );
                        }
                        break;

                case VALUE_TAG:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s%s%s",
                                        TERM(34),
                                        tags_name(ty, V_TAG(v)),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "%s",
                                        tags_name(ty, V_TAG(v))
                                );
                        }
                        break;

                case VALUE_BLOB:
                {
                        void *addr = (void *)V_BLOB(v);
                        usize size = vN(*V_BLOB(v));
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<blob at %s%p%s (%zu bytes)>%s",
                                        TERM(96),
                                        TERM(92),
                                        addr,
                                        TERM(96),
                                        size,
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "<blob at %p (%zu bytes)>", addr, size);
                        }
                        break;
                }

                case VALUE_QUEUE:
                {
                        Queue *q = V_QUEUE(v);

                        for (int i = 0; i < vN(show_queues); ++i) {
                                if (v__(show_queues, i) == q) {
                                        sxdf(&buf, "Queue([...])");
                                        goto Next;
                                }
                        }

                        xvP(show_queues, q);

                        usize n = _queue_count(q->head, q->tail, q->cap);

                        WPOP(SW_POP_QUE);
                        WLIT("])");

                        for (int i = (int)n - 1; i >= 0; --i) {
                                svP(work, q->items[(q->head + i) % q->cap]);
                                if (i > 0) {
                                        WLIT(", ");
                                }
                        }

                        WLIT("Queue([");

                        break;
                }

                case VALUE_SHARED_QUEUE:
                {
                        SharedQueue *q = V_SHARED_QUEUE(v);
                        usize n = _queue_count(q->head, q->tail, q->cap);
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<SharedQueue at %s%p%s (%zu items)>%s",
                                        TERM(96),
                                        TERM(92),
                                        (void *)q,
                                        TERM(96),
                                        n,
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "<SharedQueue at %p (%zu items)>", (void *)q, n);
                        }
                        break;
                }

                case VALUE_PTR:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<ptr:%s%s%p%s%s>%s",
                                        TERM(32),
                                        TERM(1),
                                        TERM(92),
                                        V_PTR(v),
                                        TERM(0),
                                        TERM(32),
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "<ptr:%p>", V_PTR(v));
                        }
                        break;

                case VALUE_GENERATOR:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<generator at %s%p%s>%s",
                                        TERM(96),
                                        TERM(92),
                                        V_GEN(v),
                                        TERM(96),
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "<generator at %p>", V_GEN(v));
                        }
                        break;

                case VALUE_THREAD:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<thread %"PRIu64">%s",
                                        TERM(33),
                                        V_THREAD(v)->i,
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<thread %"PRIu64">",
                                        V_THREAD(v)->i
                                );
                        }
                        break;

                case VALUE_SENTINEL:
                        sxdf(&buf, "<sentinel>");
                        break;

                case VALUE_REF:
                        sxdf(&buf, "<reference to %p>", (void *)V_REF(v));
                        break;

                case VALUE_NONE:
                        sxdf(&buf, "<none>");
                        break;

                case VALUE_TRACE:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<stack trace %s(%zu frames)%s>%s",
                                        TERM(38;2;49;161;173),
                                        TERM(34),
                                        vN(*(ThrowCtx *)V_PTR(v)),
                                        TERM(38;2;49;161;173),
                                        TERM(0)
                                );
                        } else {
                                byte_vector tmp = {0};
                                svR(tmp, 2048 * 2048);
                                char *s = FormatTrace(ty, V_PTR(v), &tmp);
                                u32 len = strlen(s);
                                if (s != NULL) {
                                        svPn(buf, s, len);
                                }
                        }
                        break;

                case VALUE_INDEX:
                        sxdf(
                                &buf,
                                "<index: (%"PRIiMAX", %jd, %d)>",
                                V_I(v),
                                V_OFF(v),
                                V_NT(v)
                        );
                        break;

                case VALUE_OBJECT:
                {
                        Value *fp = NULL;

                        if (flags & TY_SHOW_BASIC) {
                                goto BasicObject;
                        }

                        for (int i = 0; i < vN(ty->visiting); ++i) {
                                if (*v_(ty->visiting, i) == V_OBJECT(v)) {
                                        goto BasicObject;
                                }
                        }

                        i32 meth = (flags & TY_SHOW_REPR) ? NAMES._repr_ : NAMES._str_;

                        if (color) {
#ifdef TY_NO_LOG
                                fp = class_lookup_method_i(ty, V_CLASS(v), meth);
#endif
                        } else {
                                fp = class_lookup_method_i(ty, V_CLASS(v), meth);
                        }

                        if (fp != NULL) {
                                xvP(ty->visiting, V_OBJECT(v));
                                Value self = stripped(ty, &v);
                                Value str = vm_call_method(ty, &self, fp, 0);
                                vvX(ty->visiting);
                                if (V_TYPE(str) != VALUE_STRING) {
                                        goto BasicObject;
                                }
                                svPn(buf, ss(str), sN(str));
                        } else {
BasicObject:
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<%s%s%s%s%s"
                                                " object at %s%p%s>%s",
                                                TERM(96),
                                                TERM(34),
                                                class_name(ty, V_CLASS(v)),
                                                TERM(91;1),
                                                V_OBJECT(v)->dynamic ? "*" : "",
                                                TERM(96),
                                                TERM(94),
                                                (void *)V_OBJECT(v),
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<%s object at %p>",
                                                class_name(ty, V_CLASS(v)),
                                                (void *)V_OBJECT(v)
                                        );
                                }
                        }
                        break;
                }

                case VALUE_ZERO:
                        sxdf(&buf, "<zero>");
                        break;

                case VALUE_UNINITIALIZED:
                        uninit(ty, V_SYM(v));
                        break;

                default:
                        if (color) {
                                sxdf(&buf, "%s<??>%s", TERM(91;1), TERM(0));
                        } else {
                                sxdf(&buf, "<??>");
                        }
                        break;
                }

Next:
                continue;
        }

        svP(buf, '\0');
        vXx(buf);

        if (flags & TY_SHOW_ABBREV) {
                int keep = term_fit_cols(vv(buf), vN(buf), 80);
                if (keep < vN(buf)) {
                        return sfmt(
                                "%.*s%s...%s",
                                keep,
                                vv(buf),
                                TERM(90),
                                TERM(0)
                        );
                }
        }

        return vv(buf);
}

#undef WLIT
#undef WPOP

char *
value_show_color(Ty *ty, Value const *v, u32 flags)
{
        char *str;

        WITH_SCRATCH {
                str = S2(show_impl(ty, v, flags));
        }

        return str;
}

char *
value_show(Ty *ty, Value const *v, u32 flags)
{
        char *str;

        flags |= TY_SHOW_NOCOLOR;

        WITH_SCRATCH {
                str = S2(show_impl(ty, v, flags));
        }

        return str;
}

char *
value_show_scratch(Ty *ty, Value const *v, u32 flags)
{
        return show_impl(ty, v, flags);
}

Value
value_vshow_color(Ty *ty, Value const *v, u32 flags)
{
        Value str;

        WITH_SCRATCH {
                str = vSsz(show_impl(ty, v, flags));
        }

        return str;
}

Value
value_vshow(Ty *ty, Value const *v, u32 flags)
{
        Value str;

        flags |= TY_SHOW_NOCOLOR;

        WITH_SCRATCH {
                str = vSsz(show_impl(ty, v, flags));
        }

        return str;
}

inline static int
check_cmp_result(Ty *ty, Value const *v1, Value const *v2, Value v)
{
        if (V_TYPE(v) == VALUE_NONE) {
                zP(
                        "attempt to compare incomparable values\n"
                        FMT_MORE " %sleft%s: %s"
                        FMT_MORE "%sright%s: %s\n",
                        TERM(95), TERM(0),
                        SHOW(v1),
                        TERM(95), TERM(0),
                        SHOW(v2)
                );
        }

        if (V_TYPE(v) != VALUE_INTEGER) {
                zP(
                        "non-integer returned by user-defined <=> operator\n"
                        FMT_MORE "  %sleft%s: %s"
                        FMT_MORE " %sright%s: %s"
                        FMT_MORE "%sresult%s: %s\n",
                        TERM(95), TERM(0),
                        SHOW(v1),
                        TERM(95), TERM(0),
                        SHOW(v2),
                        TERM(95), TERM(0),
                        SHOW(&v)
                );
        }

        return V_Z(v);
}

int
value_compare(Ty *ty, Value const *v1, Value const *v2)
{
        int c;

        switch (PACK_TYPES(V_TYPE(*v1) & ~VALUE_TAGGED, V_TYPE(*v2) & ~VALUE_TAGGED)) {
        case PAIR_OF(VALUE_INTEGER):
                return (V_Z(*(v1)) < V_Z(*(v2))) ? -1 : (V_Z(*(v1)) != V_Z(*(v2)));

        case PAIR_OF(VALUE_REAL):
                return (V_REAL(*(v1)) < V_REAL(*(v2))) ? -1 : (V_REAL(*(v1)) != V_REAL(*(v2)));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                return (V_REAL(*(v1)) < V_Z(*(v2))) ? -1 : (V_REAL(*(v1)) != V_Z(*(v2)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                return (V_Z(*(v1)) < V_REAL(*(v2))) ? -1 : (V_Z(*(v1)) != V_REAL(*(v2)));

        case PAIR_OF(VALUE_STRING):
                c = memcmp(ss(*v1), ss(*v2), min(sN(*v1), sN(*v2)));
                return (c != 0) ? c : (int)((isize)sN(*v1) - (isize)sN(*v2));

        case PAIR_OF(VALUE_PTR):
                return ((uptr)V_PTR(*(v1)) < (uptr)V_PTR(*(v2)))
                     ? -1
                     :  ((uptr)V_PTR(*(v1)) != (uptr)V_PTR(*(v2)))
                     ;

        case PAIR_OF(VALUE_ARRAY):
                for (int i = 0; i < V_ARRAY(*(v1))->count && i < V_ARRAY(*(v2))->count; ++i) {
                        int o = value_compare(ty, &V_ARRAY(*(v1))->items[i], &V_ARRAY(*(v2))->items[i]);
                        if (o != 0)
                                return o;
                }
                return ((ptrdiff_t)V_ARRAY(*(v1))->count) - ((ptrdiff_t)V_ARRAY(*(v2))->count);

        case PAIR_OF(VALUE_TUPLE):
                if (V_ITEMS(*(v1)) == V_ITEMS(*(v2))) {
                        return 0;
                }
                if (V_IDS(*(v1)) != NULL && V_IDS(*(v2)) != NULL) {
                        return compare_records(ty, v1, v2);
                }
                for (int i = 0; i < V_COUNT(*(v1)) && i < V_COUNT(*(v2)); ++i) {
                        int o = value_compare(ty, &V_ITEMS(*(v1))[i], &V_ITEMS(*(v2))[i]);
                        if (o != 0) {
                                return o;
                        }
                }
                return ((int)V_COUNT(*(v1))) - ((int)V_COUNT(*(v2)));
        }

        return check_cmp_result(ty, v1, v2, vm_try_2op(ty, OP_CMP, v1, v2));
}

bool
value_apply_predicate(Ty *ty, Value *p, Value *v)
{
        Value b;
        char err[256];

        switch (V_TYPE(*(p))) {
        case VALUE_REGEX:
        {
                if (UNLIKELY(V_TYPE(*v) != VALUE_STRING)) {
                        zP("regex applied as predicate to non-string");
                }

                int rc = pcre2_match(
                        V_REGEX(*(p))->pcre2,
                        (PCRE2_SPTR)ss(*v),
                        sN(*v),
                        0,
                        0,
                        ty->pcre2.match,
                        ty->pcre2.ctx
                );

                if (UNLIKELY(rc < PCRE2_ERROR_NOMATCH)) {
                        pcre2_get_error_message(rc, (uint8_t *)err, sizeof err);
                        zP("apply_predicate(): PCRE2 error: %s", err);
                }

                return (rc != PCRE2_ERROR_NOMATCH);
        }

        case VALUE_TAG:
                return (tags_first(ty, V_TAGS(*(v))) == V_TAG(*(p)));

        case VALUE_CLASS:
                return (V_TYPE(*(v)) == VALUE_OBJECT) && (V_CLASS(*(v)) == V_CLASS(*(p)));

        default:
                b = vm_call1(ty, p, v);
                return value_truthy(ty, &b);
        }
}

bool
value_test_equality(Ty *ty, Value const *v1, Value const *v2)
{
        if (V_TAGS(*(v1)) != V_TAGS(*(v2))) {
                return false;
        }

        int t0 = V_TYPE(*(v1)) & ~VALUE_TAGGED;
        int t1 = V_TYPE(*(v2)) & ~VALUE_TAGGED;

        switch (PACK_TYPES(t0, t1)) {
        case PAIR_OF(VALUE_INTEGER):
                return V_Z(*(v1)) == V_Z(*(v2));

        case PAIR_OF(VALUE_STRING):
                return (sN(*v1) == sN(*v2))
                    && (memcmp(ss(*v1), ss(*v2), sN(*v1)) == 0);

        case PAIR_OF(VALUE_BOOLEAN):
                return (V_BOOL(*(v1)) == V_BOOL(*(v2)));

        case PAIR_OF(VALUE_ARRAY):
                return arrays_equal(ty, v1, v2);

        case PAIR_OF(VALUE_TUPLE):
                return tuples_equal(ty, v1, v2);

        case PAIR_OF(VALUE_DICT):
                return (V_DICT(*(v1)) == V_DICT(*(v2)));

        case PAIR_OF(VALUE_CLASS):
                return (V_CLASS(*(v1)) == V_CLASS(*(v2)));

        case PAIR_OF(VALUE_TAG):
                return (V_TAG(*(v1)) == V_TAG(*(v2)));

        case PAIR_OF(VALUE_PTR):
                return (V_PTR(*(v1)) == V_PTR(*(v2)));

        case PAIR_OF(VALUE_BLOB):
                return (V_BLOB(*(v1)) == V_BLOB(*(v2)));

        case PAIR_OF(VALUE_QUEUE):
        {
                Queue *q1 = V_QUEUE(*(v1)), *q2 = V_QUEUE(*(v2));
                if (q1 == q2) return true;
                usize n1 = _queue_count(q1->head, q1->tail, q1->cap);
                usize n2 = _queue_count(q2->head, q2->tail, q2->cap);
                if (n1 != n2) return false;
                for (usize i = 0; i < n1; ++i) {
                        Value a = q1->items[(q1->head + i) % q1->cap];
                        Value b = q2->items[(q2->head + i) % q2->cap];
                        if (!value_test_equality(ty, &a, &b)) return false;
                }
                return true;
        }

        case PAIR_OF(VALUE_SHARED_QUEUE):
                return (V_SHARED_QUEUE(*(v1)) == V_SHARED_QUEUE(*(v2)));

        case PAIR_OF(VALUE_FUNCTION):
                return (V_INFO(*(v1)) == V_INFO(*(v2)));

        case PAIR_OF(VALUE_BUILTIN_FUNCTION):
                return (V_BUILTIN_FUNCTION(*(v1)) == V_BUILTIN_FUNCTION(*(v2)));

        case PAIR_OF(VALUE_BUILTIN_METHOD):
                return (V_BUILTIN_METHOD(*v1) == V_BUILTIN_METHOD(*v2))
                    && (V_THIS(*(v1)) == V_THIS(*(v2)));

        case PAIR_OF(VALUE_REGEX):
                return V_REGEX(*(v1)) == V_REGEX(*(v2));

        case PAIR_OF(VALUE_REAL):
                return V_REAL(*(v1)) == V_REAL(*(v2));

        case PAIR_OF(VALUE_NIL):
                return true;

        case PAIR_OF(VALUE_OBJECT):
                if (V_OBJECT(*(v1)) == V_OBJECT(*(v2))) {
                        return true;
                }
                break;
        }

        if ((t0 == VALUE_NIL) || (t1 == VALUE_NIL)) {
                return false;
        }

        Value v = vm_try_2op(ty, OP_EQL, v1, v2);

        if (V_TYPE(v) != VALUE_NONE) {
                return value_truthy(ty, &v);
        }

        v = vm_try_2op(ty, OP_CMP, v1, v1);

        if (V_TYPE(v) == VALUE_NONE) {
                return false;
        }

        return check_cmp_result(ty, v1, v2, v) == 0;
}

inline static void
value_array_mark(Ty *ty, struct array *a)
{
        if (MARKED(a)) return;

        MARK(a);

#if defined(TY_TRACE_GC)
        if (a->items != NULL) {
                ADD_REACHED(ALLOC_OF(a->items)->size);
        }
#endif

        for (int i = 0; i < a->count; ++i) {
                MarkNext(ty, &a->items[i]);
        }
}

inline static void
mark_tuple_descriptor(Ty *ty, TupleValue *tuple)
{
        if (MARKED(tuple)) return;
        MARK(tuple);

        if (tuple->owner != NULL) {
                mark_tuple_descriptor(ty, tuple->owner);
                return;
        }

        if (tuple->items == NULL) return;

        if (tuple->items_gc) MARK(tuple->items);

        for (int i = 0; i < tuple->count; ++i) {
                MarkNext(ty, &tuple->items[i]);
        }

        if (tuple->ids != NULL && tuple->ids_gc) MARK(tuple->ids);
}

inline static void
mark_tuple(Ty *ty, Value const *v)
{
        mark_tuple_descriptor(ty, value_direct_tuple_ptr(*v));
}

inline static void
mark_thread(Ty *ty, Value const *v)
{
        if (MARKED(V_THREAD(*v))) return;
        MARK(V_THREAD(*v));
        MarkNext(ty, &V_THREAD(*(v))->v);
        if (V_THREAD(*v)->ctx != NULL) {
                for (Value *p = V_THREAD(*v)->ctx; V_TYPE(*p) != VALUE_NONE; ++p) {
                        MarkNext(ty, p);
                }
        }
}

inline static void
mark_string(Ty *ty, Value const *v)
{
        if (!V_RO(*v) && !V_INLINE_BYTES(*v) && V_STR0(*v) != NULL) {
                MARK(V_STR0(*v));
        }
}

inline static void
mark_generator(Ty *ty, Value const *v)
{
        if (MARKED(V_GEN(*v))) return;

        MARK(V_GEN(*v));

        MarkNext(ty, &V_GEN(*(v))->f);

        co_state *st = V_GEN(*(v))->st;

        for (int i = 0; i < vN(st->stack) + st->rc && i < vC(st->stack); ++i) {
                MarkNext(ty, v_(st->stack, i));
        }

        for (int i = 0; i < vN(st->frames); ++i) {
                MarkNext(ty, &v_(st->frames, i)->f);
        }

        for (int i = 0; i < vN(st->targets); ++i) {
                Target *target = v_(st->targets, i);
                if (target->gc != NULL) {
                        MARK(target->gc);
                }
        }

        for (int i = 0; i < vN(st->try_stack); ++i) {
                struct try *t = v__(st->try_stack, i);
                for (int i = 0; i < vN(t->defer); ++i) {
                        MarkNext(ty, v_(t->defer, i));
                }
        }

        for (int i = 0; i < vN(st->to_drop); ++i) {
                MarkNext(ty, v_(st->to_drop, i));
        }

        for (int i = 0; i < vN(st->gc_roots); ++i) {
                MarkNext(ty, v_(st->gc_roots, i));
        }
}

inline static void
mark_function(Ty *ty, Value const *v)
{
        int n = V_INFO(*(v))[FUN_INFO_CAPTURES]
              + ((V_TYPE(*(v)) & ~VALUE_TAGGED) == VALUE_BOUND_FUNCTION);

        if (from_eval(v)) {
                MARK(V_INFO(*v));
        }

        if (has_meta(v)) {
                Value *meta = meta_of(ty, v);
                if (!MARKED(meta)) {
                        MARK(meta);
                        MarkNext(ty, meta);
                }
        }

        if (V_XINFO(*(v)) != NULL) {
                MARK(V_XINFO(*v));
        }

        if (n == 0 || MARKED(V_ENV(*v))) {
                return;
        }

        MARK(V_ENV(*v));

        for (int i = 0; i < n; ++i) {
                if (V_ENV(*(v))[i] != NULL) {
                        MARK(V_ENV(*v)[i]);
                        MarkNext(ty, V_ENV(*(v))[i]);
                }
        }
}

inline static void
mark_method(Ty *ty, Value const *v)
{
        MARK(V_THIS(*v));
        MarkNext(ty, V_THIS(*(v)));
}

inline static void
mark_pointer(Ty *ty, Value const *v)
{
        if (V_GCPTR(*(v)) != NULL) {
                MARK(V_GCPTR(*v));
                switch (ALLOC_OF(V_GCPTR(*v))->type) {
                case GC_VALUE:
                        MarkNext(ty, (Value *)V_GCPTR(*(v)));
                        break;

                case GC_FFI_AUTO:
                        MarkNext(ty, &((Value *)V_GCPTR(*v))[0]);
                        MarkNext(ty, &((Value *)V_GCPTR(*v))[1]);
                        break;
                }
        }
}

inline static void
mark_trace(Ty *ty, ThrowCtx *ctx)
{
        if (MARKED(ctx)) {
                return;
        }

        MARK(ctx);

        if (DetailedExceptions) {
                for (int i = 0; i < vN(*ctx); ++i) {
                        ValueVector *locals = v_(ctx->locals, i);
                        vfor(*locals, MarkNext(ty, it));
                }
        }
}

static inline void
_value_mark_xd(Ty *ty, Value const *v)
{
        /* Deal with direct values before the generic boxed path.  Besides
         * avoiding repeated tag decoding for the common cases, this keeps a
         * direct tuple's low-bit-tagged pointer away from value_box_ptr(). */
        if (value_is_direct_array(*v)) {
                value_array_mark(ty, value_direct_array_ptr(*v));
                return;
        }
        if (value_is_direct_class(*v)) {
                class_mark(ty, value_direct_class_id(*v));
                return;
        }
        if (value_is_direct_object(*v)) {
                object_mark(ty, value_direct_object_ptr(*v));
                return;
        }
        if (nanbox_is_aux(v->bits)) return;
        if (value_is_direct_tuple(*v)) {
                mark_tuple(ty, v);
                return;
        }
        if (!nanbox_is_pointer(v->bits)) return;

        /* A marked box has already had its unique payload traced, so repeated
         * references need no further work. */
        ValueBox *box = value_box_ptr(*v);
        if (MARKED(box)) return;
        MARK(box);

        void **src = source_lookup(ty, box->payload.src);
        if (src != NULL && *src != NULL) {
                MARK(*src);
        }

#ifndef TY_RELEASE
        static _Thread_local int d;

        GC_STOP();
        //GCLOG("Marking: %s", SHOW(v, BASIC));
        GC_RESUME();

        ++d;
#endif

        switch (box->payload.type & ~VALUE_TAGGED) {
        case VALUE_METHOD:           if (!MARKED(V_THIS(*v))) { mark_method(ty, v); }                     break;
        case VALUE_BUILTIN_METHOD:   if (!MARKED(V_THIS(*v))) { MARK(V_THIS(*v)); MarkNext(ty, V_THIS(*(v))); }   break;
        case VALUE_FOREIGN_FUNCTION: if (V_XINFO(*(v)) != NULL) { MARK(V_XINFO(*v)); }                         break;
        case VALUE_ARRAY:            value_array_mark(ty, V_ARRAY(*(v)));                                   break;
        case VALUE_TUPLE:            mark_tuple(ty, v);                                                break;
        case VALUE_DICT:             dict_mark(ty, V_DICT(*(v)));                                           break;
        case VALUE_NATIVE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
        case VALUE_FUNCTION:         mark_function(ty, v);                                             break;
        case VALUE_GENERATOR:        mark_generator(ty, v);                                            break;
        case VALUE_THREAD:           mark_thread(ty, v);                                               break;
        case VALUE_STRING:           mark_string(ty, v);                                               break;
        case VALUE_OBJECT:           object_mark(ty, V_OBJECT(*(v)));                                       break;
        case VALUE_CLASS:            class_mark(ty, V_CLASS(*(v)));                                         break;
        case VALUE_REF:              MARK(V_REF(*v)); MarkNext(ty, V_REF(*(v)));                               break;
        case VALUE_BLOB:             MARK(V_BLOB(*v));                                                    break;
        case VALUE_QUEUE:            queue_mark(ty, V_QUEUE(*(v)));                                         break;
        case VALUE_SHARED_QUEUE:     shared_queue_mark(ty, V_SHARED_QUEUE(*(v)));                           break;
        case VALUE_PTR:              mark_pointer(ty, v);                                              break;
        case VALUE_TRACE:            mark_trace(ty, V_PTR(*(v)));                                           break;
        case VALUE_REGEX:            if (V_REGEX(*(v))->gc) MARK(V_REGEX(*v));                                 break;
        default:                                                                                       break;
        }

#ifndef TY_RELEASE
        --d;
#endif
}

void
_value_mark(Ty *ty, Value const *v)
{
        RESET_REACHED();

        _value_mark_xd(ty, v);

        while (vN(ty->marking) > 0) {
                v = vXx(ty->marking);
                _value_mark_xd(ty, v);
        }
}

Blob *
value_blob_new(Ty *ty)
{
        return mAo0(sizeof (Blob), GC_BLOB);
}

Value
value_tuple(Ty *ty, int n)
{
        Value tuple = value_tuple_alloc(ty, n, false);

        for (int i = 0; i < n; ++i) {
                V_ITEMS(tuple)[i] = NIL;
        }

        return tuple;
}

Value
value_record(Ty *ty, int n)
{
        Value tuple = value_tuple_alloc(ty, n, true);

        for (int i = 0; i < n; ++i) {
                V_ITEMS(tuple)[i] = NIL;
                V_IDS(tuple)[i] = -1;
        }

        return tuple;
}

Value
value_named_tuple(Ty *ty, char const *first, ...)
{
        va_list ap;
        va_start(ap, first);

        int n = 0;

        do {
                va_arg(ap, Value);
                n += 1;
        } while (va_arg(ap, char const *) != NULL);

        va_end(ap);

        Value tuple = value_tuple_alloc(ty, n, true);
        Value *items = V_ITEMS(tuple);
        int *ids = V_IDS(tuple);

        va_start(ap, first);

        ids[0] = (first[0] == '\0') ? -1 : M_ID(first);
        items[0] = va_arg(ap, Value);

        for (int i = 1; i < n; ++i) {
                char const *name = va_arg(ap, char *);
                items[i] = va_arg(ap, Value);
                ids[i] = (name[0] == '\0') ? -1 : M_ID(name);
        }

        va_end(ap);

        return tuple;
}

Value *
tuple_get_i(Value const *tuple, int id)
{
        if (V_IDS(*(tuple)) == NULL) {
                return NULL;
        }

        for (int i = 0; i < V_COUNT(*(tuple)); ++i) {
                if (V_IDS(*(tuple))[i] == id) {
                        return &V_ITEMS(*(tuple))[i];
                }
        }

        return NULL;
}

Value *
tuple_get(Value const *tuple, char const *name)
{
        return tuple_get_i(tuple, M_ID(name));
}

void
value_array_extend(Ty *ty, Array *a, Array const *other)
{
        isize n = vN(*a) + vN(*other);

        if (n != 0) {
                vvR(*a, n);
        }

        if (other->count != 0) {
                memcpy(a->items + a->count, other->items, other->count * sizeof (Value));
        }

        a->count = n;
}

int
tuple_get_completions(Ty *ty, Value const *v, char const *prefix, char **out, int max)
{
        int n = 0;
        int prefix_len = strlen(prefix);

        if (V_IDS(*(v)) == NULL) return 0;

        for (int i = 0; i < V_COUNT(*(v)) && n < max; ++i) {
                if (V_IDS(*(v))[i] == -1) continue;
                char const *name = M_NAME(V_IDS(*v)[i]);
                if (strncmp(name, prefix, prefix_len) == 0) {
                        out[n++] = S2(name);
                }
        }

        return n;
}

Value
(NewInstance)(Ty *ty, int c, ...)
{
        Class *class = class_get(ty, c);
        Value object = RawObject(c);

        va_list ap;
        va_start(ap, c);

        int argc = 0;

        for (;; ++argc) {
                Value arg = va_arg(ap, Value);

                if (IsNone(arg)) {
                        break;
                }

                vmP(&arg);
        }

        if (!IsMissing(class->init)) {
                (void)vm_call_method(ty, &object, &class->init, argc);
        }

        return object;
}

struct timespec
tuple_timespec(Ty *ty, char const *func, Value const *v)
{
        Value *sec = tuple_get(v, "sec");

        if (sec == NULL || V_TYPE(*(sec)) != VALUE_INTEGER) {
                zP(
                        "%s: expected timespec %s%s%s to have Int field %s%s%s",
                        func,
                        TERM(93),
                        VSC(v),
                        TERM(0),
                        TERM(92),
                        "sec",
                        TERM(0)
                );
        }

        Value *nsec = tuple_get(v, "nsec");

        if (nsec == NULL || V_TYPE(*(nsec)) != VALUE_INTEGER) {
                zP(
                        "%s: expected timespec %s%s%s to have Int field %s%s%s",
                        func,
                        TERM(93),
                        VSC(v),
                        TERM(0),
                        TERM(92),
                        "nsec",
                        TERM(0)
                );
        }

        return (struct timespec) {
                .tv_sec = V_Z(*(sec)),
                .tv_nsec = V_Z(*(nsec))
        };
}

Value
ConstructPrimitive(Ty *ty, int class_id, int argc, Value *kwargs)
{
        switch (class_id) {
        case CLASS_INT:
                return builtin_int(ty, argc, kwargs);

        case CLASS_FLOAT:
                return builtin_float(ty, argc, kwargs);

        case CLASS_STRING:
                return builtin_str(ty, argc, kwargs);

        case CLASS_BLOB:
                return builtin_blob(ty, argc, kwargs);

        case CLASS_ARRAY:
                return builtin_array(ty, argc, kwargs);

        case CLASS_DICT:
                return builtin_dict(ty, argc, kwargs);

        case CLASS_QUEUE:
                return builtin_queue(ty, argc, kwargs);

        case CLASS_SHARED_QUEUE:
                return builtin_shared_queue(ty, argc, kwargs);

        case CLASS_REGEX:
                return builtin_regex(ty, argc, kwargs);

        case CLASS_REGEXV:
                return builtin_regexv(ty, argc, kwargs);

        case CLASS_OBJECT:
                return builtin_object(ty, argc, kwargs);

        case CLASS_TUPLE:
                return builtin_tuple(ty, argc, kwargs);

        case CLASS_MODULE:
                return builtin_ty_mod_load(ty, argc, kwargs);

        case CLASS_PTR:
        {
                ASSERT_ARGC("Ptr.init()", 1);
                return PTR((void *)(iptr)INT_ARG(0));
        }

        case CLASS_CLASS:
                zP("Class() is not implemented");

        case CLASS_TAG:
                zP("Tag() is not implemented");

        case CLASS_FUNCTION:
                zP("Function() is not implemented");

        case CLASS_GENERATOR:
                zP("Generator() is not implemented");

        default:
                zP("unknown primitive type: %s", class_name(ty, class_id));
        }

        UNREACHABLE();
}

Value
PrettySource(Ty *ty, Value const *v)
{
        Module *mod;
        isize start;
        isize end;

        Expr *expr;
        Stmt *stmt;

        switch (V_TYPE(*(v))) {
        case VALUE_METHOD:
                expr = expr_of(V_METHOD(*v));
                mod = expr->mod;
                start = expr->start.byte;
                end = expr->end.byte;
                break;

        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
        case VALUE_NATIVE_FUNCTION:
                expr = expr_of(v);
                mod = expr->mod;
                start = expr->start.byte;
                end = expr->end.byte;
                break;

        case VALUE_CLASS:
                stmt = class_get(ty, V_CLASS(*(v)))->def;
                mod = stmt->mod;
                start = stmt->start.byte;
                end = stmt->end.byte;
                break;

        defaut:
                return NIL;
        }

        if (mod == NULL || mod->source == NULL) {
                return NIL;
        }

        byte_vector buf = {0};

        while (start > 0 && mod->source[start - 1] != '\n') {
                --start;
        }

        if (ColorOutput) {
                syntax_highlight(ty, &buf, mod, start, end, NULL, NULL);
        } else {
                sxdf(&buf, "%.*s", (int)(end - start), mod->source + start);
        }

        if (vN(buf) == 0) {
                return NIL;
        }

        return vSs(vv(buf), vN(buf));
        
}

/* vim: set sts=8 sw=8 expandtab: */
