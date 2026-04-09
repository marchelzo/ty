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
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_BOOLEAN:
        case VALUE_INTEGER:
        case VALUE_REAL:
        case VALUE_NIL:
        case VALUE_TAG:
                return true;

        case VALUE_STRING:
                return v->ro;

        case VALUE_FUNCTION:
                return (v->env == NULL && v->xinfo == NULL);

        default:
                return false;
        }
}

static iptr
ident(Value const *v)
{
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_ARRAY:   return (iptr)v->array;
        case VALUE_DICT:    return (iptr)v->dict;
        case VALUE_OBJECT:  return (iptr)v->object;
        case VALUE_BLOB:    return (iptr)v->blob;
        case VALUE_QUEUE:   return (iptr)v->queue;
        case VALUE_TUPLE:   return (iptr)v->items;
        case VALUE_STRING:  return (iptr)v->str0;
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
                emit(ty, out, REF((void *)(iptr)ref));
                return;
        }

        usize slot = vN(*out);

        if (id != -1) {
                svP(*sv, ((SeenEntry){ .id = id, .entry = slot }));
        }

        u8 type = v->type & ~VALUE_TAGGED;

        switch (type) {
        case VALUE_STRING: {
                u8 *copy = xmA(v->bytes);
                memcpy(copy, v->str, v->bytes);
                Value e = {
                        .type  = v->type,
                        .tags  = v->tags,
                        .str   = copy,
                        .bytes = v->bytes,
                        .str0  = copy,
                        .ro    = true,
                };
                emit(ty, out, e);
                break;
        }

        case VALUE_BLOB: {
                usize n = vN(*v->blob);
                u8 *copy = xmA(n);
                memcpy(copy, vv(*v->blob), n);
                Value e = {
                        .type  = v->type,
                        .tags  = v->tags,
                        .str   = copy,
                        .bytes = n,
                };
                emit(ty, out, e);
                break;
        }

        case VALUE_ARRAY: {
                Value header = { .type = v->type, .tags = v->tags };
                header.src = v->array->count;
                emit(ty, out, header);
                for (usize i = 0; i < v->array->count; ++i) {
                        prepare(ty, out, sv, &v->array->items[i]);
                }
                break;
        }

        case VALUE_TUPLE: {
                i32 *ids = NULL;
                if (v->ids != NULL) {
                        ids = xmA(v->count * sizeof (i32));
                        memcpy(ids, v->ids, v->count * sizeof (i32));
                }
                Value header = {
                        .type  = v->type,
                        .tags  = v->tags,
                        .count = v->count,
                        .ids   = ids,
                };
                emit(ty, out, header);
                for (i32 i = 0; i < v->count; ++i) {
                        prepare(ty, out, sv, &v->items[i]);
                }
                break;
        }

        case VALUE_DICT: {
                Value header = { .type = v->type, .tags = v->tags };
                header.src = v->dict->count;
                emit(ty, out, header);
                for (DictItem *it = DictFirst(v->dict); it != NULL; it = it->next) {
                        prepare(ty, out, sv, &it->k);
                        prepare(ty, out, sv, &it->v);
                }
                prepare(ty, out, sv, &v->dict->dflt);
                break;
        }

        case VALUE_OBJECT: {
                Value header = {
                        .type   = v->type,
                        .tags   = v->tags,
                        .class  = v->class,
                        .object = (TyObject *)(uptr)v->object->nslot,
                };
                emit(ty, out, header);
                for (u32 i = 0; i < v->object->nslot; ++i) {
                        prepare(ty, out, sv, &v->object->slots[i]);
                }
                break;
        }

        case VALUE_QUEUE: {
                usize n = 0;
                Queue *q = v->queue;
                if (q->cap > 0) {
                        n = (q->tail >= q->head)
                          ? (q->tail - q->head)
                          : (q->cap - q->head + q->tail);
                }
                Value header = { .type = v->type, .tags = v->tags };
                header.src = n;
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
        u8 type = e.type & ~VALUE_TAGGED;

        if (type == VALUE_REF) {
                return msg[(uptr)e.ptr];
        }

        if (basic(&e)) {
                return e;
        }

        switch (type) {
        case VALUE_STRING: {
                u8 *s = value_string_clone(ty, e.str, e.bytes);
                xmF((void *)e.str);
                Value r = {
                        .type  = e.type,
                        .tags  = e.tags,
                        .str   = s,
                        .bytes = e.bytes,
                        .str0  = s,
                        .ro    = false,
                };
                msg[*cursor - 1] = r;
                return r;
        }

        case VALUE_BLOB: {
                Blob *b = value_blob_new(ty);
                if (e.bytes > 0) {
                        uvR(*b, e.bytes);
                        memcpy(vv(*b), e.str, e.bytes);
                        vN(*b) = e.bytes;
                }
                xmF((void *)e.str);
                Value r = BLOB(b);
                r.type = e.type;
                r.tags = e.tags;
                msg[*cursor - 1] = r;
                return r;
        }

        case VALUE_ARRAY: {
                usize n = e.src;
                Array *a = value_array_new_sized(ty, n);
                Value r = ARRAY(a);
                r.type = e.type;
                r.tags = e.tags;
                msg[*cursor - 1] = r;
                for (usize i = 0; i < n; ++i) {
                        value_array_push(ty, a, reconstruct(ty, msg, cursor));
                }
                return r;
        }

        case VALUE_TUPLE: {
                i32 n = e.count;
                Value *items = mAo(n * sizeof (Value), GC_TUPLE);
                i32 *ids = NULL;
                if (e.ids != NULL) {
                        ids = mA(n * sizeof (i32));
                        memcpy(ids, e.ids, n * sizeof (i32));
                        xmF(e.ids);
                }
                Value r = TUPLE(items, ids, n, true);
                r.type = e.type;
                r.tags = e.tags;
                msg[*cursor - 1] = r;
                for (i32 i = 0; i < n; ++i) {
                        items[i] = reconstruct(ty, msg, cursor);
                }
                return r;
        }

        case VALUE_DICT: {
                usize n = e.src;
                Dict *d = dict_new(ty);
                Value r = DICT(d);
                r.type = e.type;
                r.tags = e.tags;
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
                u32 nslot = (uptr)e.object;
                usize size = sizeof (TyObject) + nslot * sizeof (Value);
                TyObject *obj = uAo0(size, GC_OBJECT);
                obj->class = class_get(ty, e.class);
                obj->nslot = nslot;
                Value r = OBJECT(obj, e.class);
                r.type = e.type;
                r.tags = e.tags;
                msg[*cursor - 1] = r;
                for (u32 i = 0; i < nslot; ++i) {
                        obj->slots[i] = reconstruct(ty, msg, cursor);
                }
                return r;
        }

        case VALUE_QUEUE: {
                usize n = e.src;
                Queue *q = mAo0(sizeof (Queue), GC_QUEUE);
                if (n > 0) {
                        q->items = uA(n * sizeof (Value));
                        q->cap = n;
                }
                Value r = QUEUE(q);
                r.type = e.type;
                r.tags = e.tags;
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

                mrealloc(chan->items, 0);
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
        u8 type = e.type & ~VALUE_TAGGED;

        if (type == VALUE_REF || basic(&e)) {
                return;
        }

        switch (type) {
        case VALUE_STRING:
        case VALUE_BLOB:
                xmF((void *)e.str);
                break;

        case VALUE_TUPLE:
                xmF(e.ids);
                for (i32 i = 0; i < e.count; ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_ARRAY:
        case VALUE_QUEUE:
                for (usize i = 0; i < e.src; ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_DICT:
                for (usize i = 0; i < 2 * e.src + 1; ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_OBJECT:
                for (u32 i = 0; i < (uptr)e.object; ++i) {
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
