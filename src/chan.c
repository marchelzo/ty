#include "ty.h"
#include "vm.h"
#include "chan.h"
#include "dict.h"
#include "class.h"

typedef struct {
        iptr id;
        usize entry;
} SeenEntry;

typedef vec(SeenEntry) SeenVec;

static inline usize
qmask(Channel const *chan)
{
        return chan->cap - 1;
}

static inline usize
qcount(Channel const *chan)
{
        return (chan->tail - chan->head + chan->cap) & qmask(chan);
}

static bool
basic(Value const *v)
{
        switch (V_TYPE(*v) & ~VALUE_TAGGED) {
        case VALUE_BOOLEAN:
        case VALUE_INTEGER:
        case VALUE_REAL:
        case VALUE_NIL:
        case VALUE_TAG:
                return !value_is_boxed(*v);

        default:
                return false;
        }
}

static iptr
ident(Value const *v)
{
        switch (V_TYPE(*v) & ~VALUE_TAGGED) {
        case VALUE_ARRAY:   return (iptr)V_ARRAY(*v);
        case VALUE_DICT:    return (iptr)V_DICT(*v);
        case VALUE_OBJECT:  return (iptr)V_OBJECT(*v);
        case VALUE_BLOB:    return (iptr)V_BLOB(*v);
        case VALUE_QUEUE:   return (iptr)V_QUEUE(*v);
        case VALUE_TUPLE:   return (iptr)V_ITEMS(*v);
        case VALUE_STRING:  return (iptr)V_STR0(*v);
        default:            return -1;
        }
}

static i64
seen(SeenVec const *sv, iptr id)
{
        for (usize i = 0; i < vN(*sv); ++i) {
                if (v_(*sv, i)->id == id) {
                        return v_(*sv, i)->entry;
                }
        }

        return -1;
}

static void
emit(Ty *ty, ValueVector *out, Value v)
{
        svP(*out, v);
}

/*
 * Serialized channel messages outlive the sender's heap, particularly when
 * an isolated thread sends its last message and exits before the receiver
 * runs.  Keep synthetic serialization headers outside the GC heaps and free
 * them while reconstructing (or discarding) the message.
 */
static Value
wire_value(ValuePayload payload)
{
        ValueBox *box = xmA(sizeof *box);
        box->payload = payload;
        return (Value){ .bits = nanbox_from_pointer(box) };
}

static void
wire_value_free(Value value)
{
        xmF(value_box_ptr(value));
}

#define WIRE_VALUE(...) wire_value((ValuePayload){ __VA_ARGS__ })

static void
prepare(Ty *ty, ValueVector *out, SeenVec *sv, Value const *v)
{
        if (basic(v)) {
                emit(ty, out, *v);
                return;
        }

        iptr id = ident(v);
        i64 ref = (id != -1) ? seen(sv, id) : -1;

        if (ref != -1) {
                emit(ty, out, WIRE_VALUE(
                        .type = VALUE_REF,
                        .ref = (Value *)(iptr)ref
                ));
                return;
        }

        usize slot = vN(*out);

        if (id != -1) {
                svP(*sv, ((SeenEntry){ .id = id, .entry = slot }));
        }

        u8 type = V_TYPE(*v) & ~VALUE_TAGGED;

        switch (type) {
        case VALUE_BOOLEAN:
        case VALUE_INTEGER:
        case VALUE_REAL:
        case VALUE_NIL:
        case VALUE_TAG:
        case VALUE_FUNCTION:
                if (type != VALUE_FUNCTION
                || (V_ENV(*v) == NULL && V_XINFO(*v) == NULL)) {
                        emit(ty, out, wire_value(value_payload(*v)));
                } else {
                        emit(ty, out, NIL);
                }
                break;

        case VALUE_STRING: {
                u8 *copy = xmA(V_BYTES(*v));
                memcpy(copy, V_STR(*v), V_BYTES(*v));
                Value e = WIRE_VALUE(
                        .type  = V_TYPE(*v),
                        .tags  = V_TAGS(*v),
                        .str   = copy,
                        .bytes = V_BYTES(*v),
                        .str0  = copy,
                        .ro    = true,
                );
                emit(ty, out, e);
                break;
        }

        case VALUE_BLOB: {
                usize n = vN(*V_BLOB(*v));
                u8 *copy = xmA(n);
                memcpy(copy, vv(*V_BLOB(*v)), n);
                Value e = WIRE_VALUE(
                        .type  = V_TYPE(*v),
                        .tags  = V_TAGS(*v),
                        .str   = copy,
                        .bytes = n,
                );
                emit(ty, out, e);
                break;
        }

        case VALUE_ARRAY: {
                Value header = WIRE_VALUE(
                        .type = V_TYPE(*v),
                        .tags = V_TAGS(*v),
                        .src = V_ARRAY(*v)->count
                );
                emit(ty, out, header);
                for (usize i = 0; i < V_ARRAY(*v)->count; ++i) {
                        prepare(ty, out, sv, &V_ARRAY(*v)->items[i]);
                }
                break;
        }

        case VALUE_TUPLE: {
                i32 *ids = NULL;
                if (V_IDS(*v) != NULL) {
                        ids = xmA(V_COUNT(*v) * sizeof (i32));
                        memcpy(ids, V_IDS(*v), V_COUNT(*v) * sizeof (i32));
                }
                Value header = WIRE_VALUE(
                        .type  = V_TYPE(*v),
                        .tags  = V_TAGS(*v),
                        .count = V_COUNT(*v),
                        .ids   = ids,
                );
                emit(ty, out, header);
                for (i32 i = 0; i < V_COUNT(*v); ++i) {
                        prepare(ty, out, sv, &V_ITEMS(*v)[i]);
                }
                break;
        }

        case VALUE_DICT: {
                Value header = WIRE_VALUE(
                        .type = V_TYPE(*v),
                        .tags = V_TAGS(*v),
                        .src = V_DICT(*v)->count
                );
                emit(ty, out, header);
                for (DictItem *it = DictFirst(V_DICT(*v)); it != NULL; it = it->next) {
                        prepare(ty, out, sv, &it->k);
                        prepare(ty, out, sv, &it->v);
                }
                prepare(ty, out, sv, &V_DICT(*v)->dflt);
                break;
        }

        case VALUE_OBJECT: {
                Value header = WIRE_VALUE(
                        .type   = V_TYPE(*v),
                        .tags   = V_TAGS(*v),
                        .class  = V_CLASS(*v),
                        .object = (TyObject *)(uptr)V_OBJECT(*v)->nslot,
                );
                emit(ty, out, header);
                for (u32 i = 0; i < V_OBJECT(*v)->nslot; ++i) {
                        prepare(ty, out, sv, &V_OBJECT(*v)->slots[i]);
                }
                break;
        }

        case VALUE_QUEUE: {
                usize n = 0;
                Queue *q = V_QUEUE(*v);
                if (q->cap > 0) {
                        n = (q->tail >= q->head)
                          ? (q->tail - q->head)
                          : (q->cap - q->head + q->tail);
                }
                Value header = WIRE_VALUE(
                        .type = V_TYPE(*v),
                        .tags = V_TAGS(*v),
                        .src = n
                );
                emit(ty, out, header);
                for (usize i = 0; i < n; ++i) {
                        usize idx = (q->head + i) % q->cap;
                        prepare(ty, out, sv, &q->items[idx]);
                }
                break;
        }

        default:
                emit(ty, out, NIL);
                break;
        }
}

static Value
reconstruct(Ty *ty, Value *msg, usize *cursor)
{
        Value e = msg[(*cursor)++];
        u8 type = V_TYPE(e) & ~VALUE_TAGGED;

        if (type == VALUE_REF) {
                usize entry = (uptr)V_REF(e);
                wire_value_free(e);
                return msg[entry];
        }

        if (basic(&e)) {
                return e;
        }

        switch (type) {
        case VALUE_BOOLEAN:
        case VALUE_INTEGER:
        case VALUE_REAL:
        case VALUE_NIL:
        case VALUE_TAG:
        case VALUE_FUNCTION: {
                ValuePayload header = value_payload(e);
                wire_value_free(e);
                Value r = value_box(ty, header);
                msg[*cursor - 1] = r;
                return r;
        }

        case VALUE_STRING: {
                ValuePayload header = value_payload(e);
                wire_value_free(e);
                u8 *s = value_string_clone(ty, header.str, header.bytes);
                xmF((void *)header.str);
                Value r = VALUE_BOX_(
                        .type  = header.type,
                        .tags  = header.tags,
                        .str   = s,
                        .bytes = header.bytes,
                        .str0  = s,
                        .ro    = false,
                );
                msg[*cursor - 1] = r;
                return r;
        }

        case VALUE_BLOB: {
                ValuePayload header = value_payload(e);
                wire_value_free(e);
                Blob *b = value_blob_new(ty);
                if (header.bytes > 0) {
                        uvR(*b, header.bytes);
                        memcpy(vv(*b), header.str, header.bytes);
                        vN(*b) = header.bytes;
                }
                xmF((void *)header.str);
                Value r = BLOB(b);
                r = value_with_tags(ty, r, header.tags);
                msg[*cursor - 1] = r;
                return r;
        }

        case VALUE_ARRAY: {
                ValuePayload header = value_payload(e);
                wire_value_free(e);
                usize n = header.src;
                Array *a = value_array_new_sized(ty, n);
                Value r = ARRAY(a);
                r = value_with_tags(ty, r, header.tags);
                msg[*cursor - 1] = r;
                for (usize i = 0; i < n; ++i) {
                        value_array_push(ty, a, reconstruct(ty, msg, cursor));
                }
                return r;
        }

        case VALUE_TUPLE: {
                ValuePayload header = value_payload(e);
                wire_value_free(e);
                i32 n = header.count;
                Value r = value_tuple_alloc(ty, n, header.ids != NULL);
                Value *items = V_ITEMS(r);
                if (header.ids != NULL) {
                        memcpy(V_IDS(r), header.ids, n * sizeof (i32));
                        xmF(header.ids);
                }
                r = value_with_tags(ty, r, header.tags);
                msg[*cursor - 1] = r;
                for (i32 i = 0; i < n; ++i) {
                        items[i] = reconstruct(ty, msg, cursor);
                }
                return r;
        }

        case VALUE_DICT: {
                ValuePayload header = value_payload(e);
                wire_value_free(e);
                usize n = header.src;
                Dict *d = dict_new(ty);
                Value r = DICT(d);
                r = value_with_tags(ty, r, header.tags);
                msg[*cursor - 1] = r;
                for (usize i = 0; i < n; ++i) {
                        Value k = reconstruct(ty, msg, cursor);
                        Value v = reconstruct(ty, msg, cursor);
                        dict_put_value(ty, d, k, v);
                }
                d->dflt = reconstruct(ty, msg, cursor);
                return r;
        }

        case VALUE_OBJECT: {
                ValuePayload header = value_payload(e);
                wire_value_free(e);
                u32 nslot = (uptr)header.object;
                usize size = sizeof (TyObject) + nslot * sizeof (Value);
                TyObject *obj = uAo0(size, GC_OBJECT);
                obj->class = class_get(ty, header.class);
                obj->nslot = nslot;
                Value r = OBJECT(obj, header.class);
                r = value_with_tags(ty, r, header.tags);
                msg[*cursor - 1] = r;
                for (u32 i = 0; i < nslot; ++i) {
                        obj->slots[i] = reconstruct(ty, msg, cursor);
                }
                return r;
        }

        case VALUE_QUEUE: {
                ValuePayload header = value_payload(e);
                wire_value_free(e);
                usize n = header.src;
                Queue *q = mAo0(sizeof (Queue), GC_QUEUE);
                if (n > 0) {
                        q->items = uA(n * sizeof (Value));
                        q->cap = n;
                }
                Value r = QUEUE(q);
                r = value_with_tags(ty, r, header.tags);
                msg[*cursor - 1] = r;
                for (usize i = 0; i < n; ++i) {
                        q->items[i] = reconstruct(ty, msg, cursor);
                }
                q->tail = n;
                return r;
        }

        default:
                return NIL;
        }
}

static void
enqueue(Channel *chan, Value *msg)
{
        usize n = chan->cap ? qcount(chan) : 0;

        if (n + 1 >= chan->cap) {
                usize   cap = chan->cap ? chan->cap * 2 : 8;
                Value **buf = mrealloc(NULL, cap * sizeof (Value *));

                for (usize i = 0; i < n; ++i) {
                        buf[i] = chan->items[(chan->head + i) & qmask(chan)];
                }

                xmF(chan->items);
                chan->items = buf;
                chan->head  = 0;
                chan->tail  = n;
                chan->cap   = cap;
        }

        chan->items[chan->tail] = msg;
        chan->tail = (chan->tail + 1) & qmask(chan);
}

void
chan_send(Ty *ty, Channel *chan, Value v)
{
        ValueVector out = {0};
        SeenVec sv = {0};
        Value *msg;
        usize n;

        WITH_SCRATCH {
                prepare(ty, &out, &sv, &v);
                n = vN(out);
                msg = xmA(n * sizeof (Value));
                memcpy(msg, vv(out), n * sizeof (Value));
        }

        UnlockTy();
        TyMutexLock(&chan->m);
        atomic_fetch_add_explicit(&chan->waiters, 1, memory_order_acq_rel);
        enqueue(chan, msg);
        atomic_fetch_sub_explicit(&chan->waiters, 1, memory_order_acq_rel);
        TyMutexUnlock(&chan->m);
        TyCondVarSignal(&chan->c);
        LockTy();
}

static bool
dequeue(Ty *ty, Channel *chan, Value *v)
{
        if (chan->head == chan->tail) {
                atomic_fetch_sub_explicit(&chan->waiters, 1, memory_order_acq_rel);
                TyMutexUnlock(&chan->m);
                LockTy();
                return false;
        }

        Value *msg = chan->items[chan->head];
        chan->head = (chan->head + 1) & qmask(chan);

        atomic_fetch_sub_explicit(&chan->waiters, 1, memory_order_acq_rel);
        TyMutexUnlock(&chan->m);
        LockTy();

        CheckUsed(ty);
        GC_STOP();

        usize cursor = 0;
        *v = reconstruct(ty, msg, &cursor);

        GC_RESUME();

        xmF(msg);

        return true;
}

bool
chan_recv(Ty *ty, Channel *chan, Value *v)
{
        UnlockTy();
        TyMutexLock(&chan->m);
        atomic_fetch_add_explicit(&chan->waiters, 1, memory_order_acq_rel);

        while (chan->head == chan->tail && chan->open) {
                TyCondVarWait(&chan->c, &chan->m);
        }

        return dequeue(ty, chan, v);
}

bool
chan_try_recv(Ty *ty, Channel *chan, Value *v, i64 timeout)
{
        UnlockTy();
        TyMutexLock(&chan->m);
        atomic_fetch_add_explicit(&chan->waiters, 1, memory_order_acq_rel);

        if (chan->open && chan->head == chan->tail) {
                TyCondVarTimedWaitRelative(&chan->c, &chan->m, timeout);
        }

        return dequeue(ty, chan, v);
}

static void
discard(Value *msg, usize *cursor)
{
        Value e = msg[(*cursor)++];
        u8 type = V_TYPE(e) & ~VALUE_TAGGED;

        if (type == VALUE_REF) {
                wire_value_free(e);
                return;
        }

        if (basic(&e)) {
                return;
        }

        ValuePayload header = value_payload(e);
        wire_value_free(e);

        switch (type) {
        case VALUE_STRING:
        case VALUE_BLOB:
                xmF((void *)header.str);
                break;

        case VALUE_TUPLE:
                xmF(header.ids);
                for (i32 i = 0; i < header.count; ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_ARRAY:
        case VALUE_QUEUE:
                for (usize i = 0; i < header.src; ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_DICT:
                for (usize i = 0; i < 2 * header.src + 1; ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_OBJECT:
                for (u32 i = 0; i < (uptr)header.object; ++i) {
                        discard(msg, cursor);
                }
                break;
        }
}

void
chan_destroy(Ty *ty, Channel *chan)
{
        TyMutexLock(&chan->m);
        chan->open = false;
        usize n = chan->cap ? qcount(chan) : 0;
        usize h = chan->head;
        chan->head = chan->tail = 0;
        TyMutexUnlock(&chan->m);

        TyCondVarBroadcast(&chan->c);

        while (atomic_load_explicit(&chan->waiters, memory_order_acquire) != 0) {
                ;
        }

        for (usize i = 0; i < n; ++i) {
                Value *msg = chan->items[(h + i) & qmask(chan)];
                usize cursor = 0;
                discard(msg, &cursor);
                xmF(msg);
        }

        TyMutexDestroy(&chan->m);
        TyCondVarDestroy(&chan->c);
        xmF(chan->items);
}

/* vim: set sw=8 sts=8 expandtab: */
