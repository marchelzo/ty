#include <time.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <setjmp.h>
#include <stdarg.h>
#include <errno.h>
#include <stdnoreturn.h>

#include <pcre.h>
#include <poll.h>
#include <fcntl.h>
#include <unistd.h>
#include <signal.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <netdb.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <netdb.h>
#include <netinet/ip.h>

#include "vm.h"
#include "util.h"
#include "gc.h"
#include "dict.h"
#include "value.h"
#include "alloc.h"
#include "compiler.h"
#include "test.h"
#include "log.h"
#include "operators.h"
#include "array.h"
#include "str.h"
#include "blob.h"
#include "tags.h"
#include "object.h"
#include "class.h"
#include "utf8.h"
#include "functions.h"
#include "html.h"

#define TY_LOG_VERBOSE 1

#define READVALUE(s) (memcpy(&s, ip, sizeof s), (ip += sizeof s))

#if defined(TY_LOG_VERBOSE) && !defined(TY_NO_LOG)
  #define CASE(i) case INSTR_ ## i: loc = compiler_get_location(ip, &fname); LOG("%s:%d:%d: " #i, fname, loc.line + 1, loc.col + 1);
#else
  #define CASE(i) case INSTR_ ## i:
#endif

#define inline __attribute__((always_inline)) inline

static char halt = INSTR_HALT;

static jmp_buf jb;

struct try {
        jmp_buf jb;
        int sp;
        int gc;
        int cs;
        int ts;
        char *catch;
        char *finally;
        char *end;
};

struct target {
        struct value *t;
        void *gc;
};

static struct variable **vars;
static bool *used;

static vec(struct value) stack;
static vec(char *) calls;
static vec(size_t) sp_stack;
static vec(struct target) targets;
static vec(struct try) try_stack;
static char *ip;

static int symbol_count;

static char const *filename;

static char const *err_msg;
static char err_buf[8192];

static struct {
        char const *module;
        char const *name;
        struct value value;
} builtins[] = {
#include "builtins.h"
};

static int builtin_count = sizeof builtins / sizeof builtins[0];

static void
vm_exec(char *code);

inline static struct variable *
newvar(struct variable *next)
{
        struct variable *v = gc_alloc_unregistered(sizeof *v, GC_VARIABLE);
        v->captured = false;
        v->try = try_stack.count;
        v->prev = NULL;
        v->next = next;
        return v;
}

inline static void
pushvar(int s)
{
        if (vars[s] == NULL) {
                vars[s] = newvar(vars[s]);
        } else if (used[s]) {
                vars[s] = newvar(vars[s]);
                vars[s]->next->prev = vars[s];
        }
        
        vars[s]->try = try_stack.count;
        used[s] = true;
}

/*
 * This relies on no other symbols being introduced to the compiler
 * up until the point that this is called. i.e., it assumes that the
 * first built-in function should have symbol 0. I think this is ok.
 */
static void
add_builtins(int ac, char **av)
{
        resize(vars, sizeof *vars * (builtin_count + 1));
        resize(used, sizeof *used * (builtin_count + 1));

        for (int i = 0; i < builtin_count; ++i) {
                compiler_introduce_symbol(builtins[i].module, builtins[i].name);
                vars[i] = newvar(NULL);
                vars[i]->value = builtins[i].value;
                used[i] = true;
        }

        struct array *args = value_array_new();
        NOGC(args);

        for (int i = 1; i < ac; ++i)
                value_array_push(args, STRING_NOGC(av[i], strlen(av[i])));

        compiler_introduce_symbol("os", "args");
        vars[builtin_count] = newvar(NULL);
        vars[builtin_count]->value = ARRAY(args);
        used[builtin_count] = true;

        symbol_count = builtin_count + 1;
}


void
vm_load_c_module(char const *name, void *p)
{

        struct {
                char const *name;
                struct value value;
        } *mod = p;

        int n = 0;
        while (mod[n].name != NULL)
                n += 1;

        resize(vars, sizeof *vars * (symbol_count + n));
        resize(used, sizeof *used * (symbol_count + n));

        for (int i = 0; i < n; ++i) {
                compiler_introduce_symbol(name, mod[i].name);
                vars[symbol_count + i] = newvar(NULL);
                vars[symbol_count + i]->value = mod[i].value;
                used[symbol_count + i] = true;
        }

        symbol_count += n;
}

inline static struct value *
top(void)
{
        return &stack.items[stack.count] - 1;
}

inline static struct value
pop(void)
{
        LOG("POP: %s", value_show(top()));
        return *vec_pop(stack);
}

inline static struct value
peek(void)
{
        return stack.items[stack.count - 1];
}

inline static void
push(struct value v)
{
        LOG("PUSH: %s", value_show(&v));
        vec_push(stack, v);
}

inline static struct value *
poptarget(void)
{
        struct target t = *vec_pop(targets);
        if (t.gc != NULL) OKGC(t.gc);
        return t.t;
}

inline static struct value *
peektarget(void)
{
        return targets.items[targets.count - 1].t;
}

inline static void
pushtarget(struct value *v, void *gc)
{
        struct target t = { .t = v, .gc = gc };
        if (gc != NULL) NOGC(gc);
        vec_push(targets, t);
}

inline static void
call(struct value const *f, struct value const *self, int n, bool exec)
{
        for (int i = 0; i < f->bound; ++i)
                pushvar(f->symbols[i]);

        bool has_self = (f->params > 0) && (self != NULL);

        int params = f->params - has_self - f->rest;

        if (f->rest) {
                struct value v = ARRAY(value_array_new());
                for (int i = n - params - 1; i >= 0; --i)
                        value_array_push(v.array, top()[-i]);
                vars[f->symbols[f->params - 1]]->value = v;
        }

        /* throw away extra arguments */
        while (n > params) {
                pop(), --n;
        }

        /* default missing parameters to nil */
        for (int i = n; i < params; ++i)
                vars[f->symbols[i + has_self]]->value = NIL;

        /* fill in the rest of the arguments */
        while (n --> 0) {
                vars[f->symbols[n + has_self]]->value = pop();
        }

        /* fill in 'self' / 'this' */
        if (has_self)
                vars[f->symbols[0]]->value = *self;

        if (f->refs != NULL) for (int i = 0; i < f->refs->count; ++i) {
                struct reference ref = f->refs->refs[i];
                //LOG("resolving reference to %p", (void *) ref.pointer);
                memcpy(f->code + ref.offset, &ref.pointer, sizeof ref.pointer);
        }

        if (exec) {
                vec_push(calls, &halt);
                vm_exec(f->code);
        } else {
                vec_push(calls, ip);
                ip = f->code;
        }
}

static void
vm_exec(char *code)
{
        char *save = ip;
        ip = code;

        uintptr_t s, s2, off;
        intmax_t k;
        bool b;
        float f;
        int n, i, j, tag, rc = 0;
        unsigned long h;

        struct value left, right, v, key, value, container, subscript, *vp;
        char *str;

        struct value (*func)(struct value *, int);

        struct variable *next;

#ifdef TY_LOG_VERBOSE
        struct location loc;
        char const *fname;
#endif

        for (;;) {
                switch (*ip++) {
                CASE(NOP)
                        continue;
                CASE(PUSH_VAR)
                        READVALUE(s);
                        pushvar(s);
                        break;
                CASE(POP_VAR)
                        READVALUE(s);
                        next = vars[s]->next;
                        if (vars[s]->captured) {
                                gc_register(vars[s]);
                                if (vars[s]->next != NULL)
                                        vars[s]->next->prev = vars[s]->prev;
                                if (vars[s]->prev != NULL)
                                        vars[s]->prev->next = vars[s]->next;
                        }
                        if (next == NULL && !vars[s]->captured)
                                used[s] = false;
                        else
                                vars[s] = next;
                        break;
                CASE(LOAD_VAR)
                        READVALUE(s);
                        push(vars[s]->value);
                        break;
                CASE(CHECK_VARS)
                        READVALUE(n);
                        while (n --> 0) {
                                READVALUE(s);
                                if (vars[s] != NULL && vars[s]->captured) {
                                        gc_register(vars[s]);
                                        struct variable *new = newvar(vars[s]->next);
                                        new->value = vars[s]->value;
                                        new->prev = vars[s]->prev;
                                        if (new->next != NULL)
                                                new->next->prev = new;
                                        if (new->prev != NULL)
                                                new->prev->next = new;
                                        vars[s] = new;
                                }
                        }
                        break;
                CASE(EXEC_CODE)
                        READVALUE(s);
                        vm_exec((char *) s);
                        break;
                CASE(DUP)
                        push(peek());
                        break;
                CASE(JUMP)
                        READVALUE(n);
                        ip += n;
                        break;
                CASE(JUMP_IF)
                        READVALUE(n);
                        v = pop();
                        if (value_truthy(&v)) {
                                ip += n;
                        }
                        break;
                CASE(JUMP_IF_NOT)
                        READVALUE(n);
                        v = pop();
                        if (!value_truthy(&v)) {
                                ip += n;
                        }
                        break;
                CASE(JUMP_IF_NONE)
                        READVALUE(n);
                        if (top()[-1].type == VALUE_NONE) {
                                ip += n;
                        }
                        break;
                CASE(TARGET_VAR)
                        READVALUE(s);
                        pushtarget(&vars[s]->value, NULL);
                        break;
                CASE(TARGET_REF)
                        READVALUE(s);
                        pushtarget(&((struct variable *) s)->value, NULL);
                        break;
                CASE(TARGET_MEMBER)
                        v = pop();
                        if (!(v.type & VALUE_OBJECT))
                                vm_panic("assignment to member of non-object");
                        str = ip;
                        ip += strlen(ip) + 1;
                        READVALUE(h);
                        vp = table_lookup(v.object, str, h);
                        if (vp != NULL)
                                pushtarget(vp, v.object);
                        else
                                pushtarget(table_add(v.object, str, h, NIL), v.object);
                        break;
                CASE(TARGET_SUBSCRIPT)
                        subscript = pop();
                        container = pop();

                        if (container.type == VALUE_ARRAY) {
                                if (subscript.type != VALUE_INTEGER)
                                        vm_panic("non-integer array index used in subscript assignment");
                                if (subscript.integer < 0)
                                        subscript.integer += container.array->count;
                                if (subscript.integer < 0 || subscript.integer >= container.array->count)
                                        vm_panic("array index out of range in subscript expression");
                                pushtarget(&container.array->items[subscript.integer], container.array);
                        } else if (container.type == VALUE_DICT) {
                                pushtarget(dict_put_key_if_not_exists(container.dict, subscript), container.dict);
                        } else {
                                vm_panic("attempt to perform subscript assignment on something other than an object or array");
                        }
                        break;
                CASE(ASSIGN)
                        *poptarget() = peek();
                        break;
                CASE(TAG_PUSH)
                        READVALUE(tag);
                        top()->tags = tags_push(top()->tags, tag);
                        top()->type |= VALUE_TAGGED;
                        break;
                CASE(ARRAY_REST)
                        READVALUE(s);
                        READVALUE(i);
                        READVALUE(n);
                        if (top()->type != VALUE_ARRAY) {
                                LOG("cannot do rest: top is not an array");
                                ip += n;
                        } else {
                                //LOG("Assigning rest to: %d", (int) s);
                                vars[s]->value = ARRAY(value_array_new());
                                vec_push_n(*vars[s]->value.array, top()->array->items + i, top()->array->count - i);
                        }
                        break;
                CASE(THROW_IF_NIL)
                        if (top()->type == VALUE_NIL) {
                                push(TAG(tags_lookup("MatchError")));
                                goto Throw;
                        }
                        break;
                CASE(UNTAG_OR_DIE)
                        READVALUE(tag);
                        if (!tags_same(tags_first(top()->tags), tag)) {
                                push(TAG(tags_lookup("MatchError")));
                                goto Throw;
                        } else {
                                top()->tags = tags_pop(top()->tags);
                                top()->type &= ~VALUE_TAGGED;
                        }
                        break;
                CASE(BAD_MATCH)
                        push(TAG(tags_lookup("MatchError")));
                        goto Throw;
                CASE(THROW)
Throw:
                        if (try_stack.count == 0)
                                vm_panic("uncaught exception: %s", value_show(top()));

                        struct try *t = vec_last(try_stack);

                        v = pop();
                        stack.count = t->sp;
                        push(SENTINEL);
                        push(v);

                        targets.count = t->ts;
                        calls.count = t->cs;
                        ip = t->catch;

                        for (i = 0; i < symbol_count; ++i) {
                                while (vars[i] != NULL && vars[i]->try >= try_stack.count) {
                                        if (vars[i]->captured && vars[i]->next != NULL)
                                                vars[i]->next->prev = vars[i]->prev;
                                        vars[i] = vars[i]->next;
                                }
                        }

                        gc_truncate_root_set(t->gc);

                        longjmp(t->jb, 1);
                        /* unreachable */
                CASE(FINALLY)
                {
                        struct try *t = vec_pop(try_stack);
                        if (t->finally == NULL)
                                break;
                        *t->end = INSTR_HALT;
                        vm_exec(t->finally);
                        *t->end = INSTR_NOP;
                        break;
                }
                CASE(POP_TRY)
                        --try_stack.count;
                        break;
                CASE(TRY)
                {
                        READVALUE(n);
                        struct try t;
                        if (setjmp(t.jb) != 0)
                                break;
                        t.catch = ip + n;
                        READVALUE(n);
                        t.finally = (n == -1) ? NULL : ip + n;
                        READVALUE(n);
                        t.end = (n == -1) ? NULL : ip + n;
                        t.sp = stack.count;
                        t.gc = gc_root_set_count();
                        t.cs = calls.count;
                        t.ts = targets.count;
                        vec_push(try_stack, t);
                        break;
                }
                CASE(ENSURE_LEN)
                        READVALUE(n);
                        b = top()->array->count == n;
                        READVALUE(n);
                        if (!b)
                                ip += n;
                        break;
                CASE(ENSURE_EQUALS_VAR)
                        READVALUE(s);
                        READVALUE(n);
                        if (!value_test_equality(top(), &vars[s]->value))
                                ip += n;
                        break;
                CASE(TRY_ASSIGN_NON_NIL)
                        READVALUE(s);
                        READVALUE(n);
                        if (top()->type == VALUE_NIL)
                                ip += n;
                        else
                                vars[s]->value = peek();
                        break;
                CASE(TRY_REGEX)
                        READVALUE(s);
                        READVALUE(s2);
                        READVALUE(n);
                        v = REGEX((pcre *) s);
                        v.extra = (pcre_extra *) s2;
                        if (!value_apply_predicate(&v, top()))
                                ip += n;
                        break;
                CASE(TRY_INDEX)
                        READVALUE(i);
                        READVALUE(n);
                        //LOG("trying to index: %s", value_show(top()));
                        if (top()->type != VALUE_ARRAY || top()->array->count <= i)
                                ip += n;
                        else
                                push(top()->array->items[i]);
                        break;
                CASE(TRY_TAG_POP)
                        READVALUE(tag);
                        READVALUE(n);
                        if (!tags_same(top()->tags, tag)) {
                                //LOG("failed tag pop");
                                ip += n;
                        } else {
                                //LOG("tag pop successful");
                                top()->tags = tags_pop(top()->tags);
                                if (top()->tags == 0) {
                                        top()->type &= ~VALUE_TAGGED;
                                }
                        }
                        break;
                CASE(POP)
                        pop();
                        break;
                CASE(LOAD_REF)
                        READVALUE(s);
                        //LOG("reference is: %p", (void *) s);
                        push(((struct variable *) s)->value);
                        break;
                CASE(INTEGER)
                        READVALUE(k);
                        push(INTEGER(k));
                        break;
                CASE(REAL)
                        READVALUE(f);
                        push(REAL(f));
                        break;
                CASE(BOOLEAN)
                        READVALUE(b);
                        push(BOOLEAN(b));
                        break;
                CASE(STRING)
                        n = strlen(ip);
                        push(STRING_NOGC(ip, n));
                        ip += n + 1;
                        break;
                CASE(CLASS)
                        READVALUE(tag);
                        push(CLASS(tag));
                        break;
                CASE(TAG)
                        READVALUE(tag);
                        push(TAG(tag));
                        break;
                CASE(REGEX)
                        READVALUE(s);
                        v = REGEX((pcre *) s);
                        READVALUE(s);
                        v.extra = (pcre_extra *) s;
                        READVALUE(s);
                        v.pattern = (char const *) s;
                        push(v);
                        break;
                CASE(ARRAY)
                        v = ARRAY(value_array_new());

                        READVALUE(n);
                        vec_reserve(*v.array, n);
                        for (i = 0; i < n; ++i)
                                vec_push(*v.array, pop());

                        push(v);
                        break;
                CASE(DICT)
                        v = DICT(dict_new());

                        READVALUE(n);
                        for (i = 0; i < n; ++i) {
                                value = pop();
                                key = pop();
                                dict_put_value(v.dict, key, value);
                        }

                        push(v);
                        break;
                CASE(DICT_DEFAULT)
                        v = pop();
                        top()->dict->dflt = v;
                        break;
                CASE(NIL)
                        push(NIL);
                        break;
                CASE(TO_STRING)
                        v = builtin_str(1);
                        pop();
                        push(v);
                        break;
                CASE(GET_NEXT)
                        v = top()[-1];
                        i = top()[-2].i++;
                        LOG("GET_NEXT: v = %s", value_show(&v));
                        LOG("GET_NEXT: i = %d", i);
                        switch (v.type) {
                        case VALUE_ARRAY:
                                if (i < v.array->count) {
                                        push(v.array->items[i]);
                                } else {
                                        push(NONE);
                                }
                                break;
                        case VALUE_DICT:
                                off = top()[-2].off;
                                while (off < v.dict->size && v.dict->keys[off].type == 0) ++off;
                                if (off < v.dict->size) {
                                        top()[-2].off = off + 1;
                                        push(v.dict->keys[off]);
                                        push(v.dict->values[off]);
                                        rc = 1;
                                        pop();
                                } else {
                                        push(NONE);
                                }
                                break;
                        case VALUE_OBJECT:
                                if ((vp = class_method(v.class, "__next__")) != NULL) {
                                        static char next_fix[] = { INSTR_NONE_IF_NIL, INSTR_RETURN };
                                        push(INTEGER(i));
                                        vec_push(calls, ip);
                                        call(vp, &v, 1, false);
                                        *vec_last(calls) = next_fix;
                                } else if ((vp = class_method(v.class, "__iter__")) != NULL) {
                                        static char iter_fix[] = { INSTR_SENTINEL, INSTR_RETURN };
                                        pop();
                                        pop();
                                        --top()->i;
                                        /* Have to repeat this instruction */
                                        vec_push(calls, ip - 1);
                                        call(vp, &v, 0, false);
                                        *vec_last(calls) = iter_fix;
                                        continue;
                                } else {
                                        goto NoIter;
                                }
                                break;
                        case VALUE_BLOB:
                                if (i < v.blob->count) {
                                        push(INTEGER(v.blob->items[i]));
                                } else {
                                        push(NONE);
                                }
                                break;
                        case VALUE_STRING:
                                vp = top() - 2;
                                if ((off = vp->off) < v.bytes) {
                                        vp->off += (n = utf8_char_len(v.string + off));
                                        push(STRING_VIEW(v, off, n));
                                } else {
                                        push(NONE); 
                                }
                                break;
                        default:
                        NoIter:
                                vm_panic("for-each loop on non-iterable value: %s", value_show(&v));
                        }
                        break;
                CASE(ARRAY_COMPR)
                        READVALUE(n);
                        v = top()[-(n + 2)];
                        for (int i = 0; i < n; ++i)
                                value_array_push(v.array, top()[-i]);
                        stack.count -= n;
                        break;
                CASE(DICT_COMPR)
                        READVALUE(n);
                        v = top()[-(2*n + 2)];
                        for (i = 0; i < n; ++i) {
                                value = top()[-2*i];
                                key = top()[-(2*i + 1)];
                                dict_put_value(v.dict, key, value);
                        }
                        stack.count -= 2 * n;
                        break;
                CASE(PUSH_INDEX)
                        READVALUE(n);
                        push(INDEX(0, 0, n));
                        break;
                CASE(READ_INDEX)
                        k = top()[-3].integer - 1;
                        stack.count += rc;
                        push(INTEGER(k));
                        break;
                CASE(SENTINEL)
                        push(SENTINEL);
                        break;
                CASE(NONE_IF_NIL)
                        if (top()->type == VALUE_NIL)
                                *top() = NONE;
                        break;
                CASE(CLEAR_RC)
                        rc = 0;
                        break;
                CASE(GET_EXTRA)
                        stack.count += rc;
                        break;
                CASE(FIX_EXTRA)
                        for (n = 0; top()[-n].type != VALUE_SENTINEL; ++n)
                                ;
                        for (i = 0, j = n - 1; i < j; ++i, --j) {
                                v = top()[-i];
                                top()[-i] = top()[-j];
                                top()[-j] = v;
                        }
                        break;
                CASE(FIX_TO)
                        READVALUE(n);
                        for (i = 0; top()[-i].type != VALUE_SENTINEL; ++i)
                                ;
                        while (i > n)
                                --i, pop();
                        while (i < n)
                                ++i, push(NIL);
                        for (i = 0, j = n - 1; i < j; ++i, --j) {
                                v = top()[-i];
                                top()[-i] = top()[-j];
                                top()[-j] = v;
                        }
                        break;
                CASE(REVERSE)
                        for (i = 0; top()[-i].type != VALUE_SENTINEL; ++i)
                                ;
                        
                        READVALUE(n);
                        for (--n, i = 0; i < n; ++i, --n) {
                                v = top()[-i];
                                top()[-i] = top()[-n];
                                top()[-n] = v;
                        }
                        break;
                CASE(MULTI_ASSIGN)
                        READVALUE(n);
                        for (i = 0, vp = top(); pop().type != VALUE_SENTINEL; ++i)
                                ;
                        for (int j = targets.count - n; n > 0; --n, poptarget()) {
                                if (i > 0) {
                                        *targets.items[j++].t = vp[-(--i)];
                                } else {
                                        *targets.items[j++].t = NIL;
                                }
                        }
                        push(top()[2]);
                        break;
                CASE(JUMP_IF_SENTINEL)
                        READVALUE(n);
                        if (top()->type == VALUE_SENTINEL)
                                ip += n;
                        break;
                CASE(CLEAR_EXTRA)
                        while (top()->type != VALUE_SENTINEL)
                                pop();
                        pop();
                        break;
                CASE(PUSH_NTH)
                        READVALUE(n);
                        push(top()[-n]);
                        break;
                CASE(CONCAT_STRINGS)
                        READVALUE(n);
                        k = 0;
                        for (i = stack.count - n; i < stack.count; ++i)
                                k += stack.items[i].bytes;
                        str = value_string_alloc(k);
                        v = STRING(str, k);
                        k = 0;
                        for (i = stack.count - n; i < stack.count; ++i) {
                                memcpy(str + k, stack.items[i].string, stack.items[i].bytes);
                                k += stack.items[i].bytes;
                        }
                        stack.count -= n - 1;
                        stack.items[stack.count - 1] = v;
                        break;
                CASE(RANGE)
                        right = pop();
                        left = pop();

                        i = class_lookup("Range");
                        if (i == -1 || (vp = class_method(i, "init")) == NULL) {
                                vm_panic("failed to load Range class. was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(), i);
                        push(left);
                        push(right);
                        call(vp, &v, 2, true);
                        pop();
                        push(v);
                        break;
                CASE(INCRANGE)
                        right = pop();
                        left = pop();

                        i = class_lookup("InclusiveRange");
                        if (i == -1 || (vp = class_method(i, "init")) == NULL) {
                                vm_panic("failed to load InclusiveRange class. was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(), i);
                        push(left);
                        push(right);
                        call(vp, &v, 2, true);
                        pop();
                        push(v);
                        break;
                CASE(MEMBER_ACCESS)
                        v = pop();

                        char const *member = ip;
                        ip += strlen(ip) + 1;

                        READVALUE(h);

                        vp = NULL;
                        if (v.type & VALUE_TAGGED) for (int tags = v.tags; tags != 0; tags = tags_pop(tags)) {
                                vp = tags_lookup_method(tags_first(tags), member, h);
                                if (vp != NULL)  {
                                        struct value *this = gc_alloc_object(sizeof *this, GC_VALUE);
                                        *this = v;
                                        this->tags = tags;
                                        push(METHOD(member, vp, this));
                                        break;
                                }
                        }

                        if (vp != NULL)
                                break;

                        struct value *this;

                        switch (v.type & ~VALUE_TAGGED) {
                        case VALUE_NIL:
                                push(NIL);
                                break;
                        case VALUE_DICT:
                                func = get_dict_method(member);
                                if (func == NULL)
                                        vm_panic("reference to non-existent method '%s' on dict", member);
                                v.type = VALUE_ARRAY;
                                v.tags = 0;
                                this = gc_alloc_object(sizeof *this, GC_VALUE);
                                *this = v;
                                push(BUILTIN_METHOD(member, func, this));
                                break;
                        case VALUE_ARRAY:
                                func = get_array_method(member);
                                if (func == NULL)
                                        vm_panic("reference to non-existent method '%s' on array", member);
                                v.type = VALUE_ARRAY;
                                v.tags = 0;
                                this = gc_alloc_object(sizeof *this, GC_VALUE);
                                *this = v;
                                push(BUILTIN_METHOD(member, func, this));
                                break;
                        case VALUE_STRING:
                                func = get_string_method(member);
                                if (func == NULL)
                                        vm_panic("reference to non-existent method '%s' on string", member);
                                v.type = VALUE_STRING;
                                v.tags = 0;
                                this = gc_alloc_object(sizeof *this, GC_VALUE);
                                *this = v;
                                push(BUILTIN_METHOD(member, func, this));
                                break;
                        case VALUE_BLOB:
                                func = get_blob_method(member);
                                if (func == NULL)
                                        vm_panic("reference to non-existent method '%s' on blob", member);
                                v.type = VALUE_BLOB;
                                v.tags = 0;
                                this = gc_alloc_object(sizeof *this, GC_VALUE);
                                *this = v;
                                push(BUILTIN_METHOD(member, func, this));
                                break;
                        case VALUE_OBJECT:
                                vp = table_lookup(v.object, member, h);
                                if (vp != NULL) {
                                        push(*vp);
                                        break;
                                }
                                vp = class_lookup_method(v.class, member, h);
                                if (vp != NULL) {
                                        this = gc_alloc_object(sizeof *this, GC_VALUE);
                                        *this = v;
                                        push(METHOD(member, vp, this));
                                        break;
                                }
                                vm_panic("attempt to access non-existent member '%s' of %s", member, value_show(&v));
                                break;
                        case VALUE_TAG:
                                vp = tags_lookup_method(v.tag, member, h);
                                push(vp == NULL ? NIL : *vp);
                                break;
                        case VALUE_CLASS:
                                vp = class_lookup_method(v.class, member, h);
                                push(vp == NULL ? NIL : *vp);
                                break;
                        default:
                                vm_panic("member access on value of invalid type: %s", value_show(&v));
                        }

                        break;
                CASE(SUBSCRIPT)
                        subscript = pop();
                        container = pop();

                        switch (container.type) {
                        case VALUE_ARRAY:
                                if (subscript.type == VALUE_OBJECT) {
ObjectSubscript:
                                        vp = class_method(subscript.class, "__next__");
                                        if (vp == NULL) {
                                                vp = class_method(subscript.class, "__iter__");
                                                if (vp == NULL) {
                                                        vm_panic("non-iterable object used in subscript expression");
                                                }
                                                call(vp, &subscript, 0, true);
                                                subscript = pop();
                                                goto ObjectSubscript;
                                        }
                                        struct array *a = value_array_new();
                                        NOGC(a);
                                        for (int i = 0; ; ++i) {
                                                push(INTEGER(i));
                                                call(vp, &subscript, 1, true);
                                                struct value r = pop();
                                                if (r.type == VALUE_NIL)
                                                        break;
                                                if (r.type != VALUE_INTEGER)
                                                        vm_panic("iterator yielded non-integer array index in subscript expression");
                                                if (r.integer < 0)
                                                        r.integer += container.array->count;
                                                if (r.integer < 0 || r.integer >= container.array->count)
                                                        goto OutOfRange;
                                                value_array_push(a, container.array->items[r.integer]);
                                        }
                                        push(ARRAY(a));
                                        OKGC(a);
                                } else if (subscript.type == VALUE_INTEGER) {
                                        if (subscript.integer < 0)
                                                subscript.integer += container.array->count;
                                        if (subscript.integer < 0 || subscript.integer >= container.array->count)
OutOfRange:
                                                vm_panic("array index out of range in subscript expression");
                                        push(container.array->items[subscript.integer]);
                                } else {
                                        vm_panic("non-integer array index used in subscript expression");
                                }
                                break;
                        case VALUE_STRING:
                                push(subscript);
                                v = get_string_method("char")(&container, 1);
                                pop();
                                push(v);
                                break;
                        case VALUE_BLOB:
                                push(subscript);
                                v = get_blob_method("get")(&container, 1);
                                pop();
                                push(v);
                                break;
                        case VALUE_DICT:
                                vp = dict_get_value(container.dict, &subscript);
                                push((vp == NULL) ? NIL : *vp);
                                break;
                        case VALUE_NIL:
                                push(NIL);
                                break;
                        default:
                                vm_panic("attempt to subscript something other than an object or array");
                        }
                        break;
                CASE(NOT)
                        v = pop();
                        push(unary_operator_not(&v));
                        break;
                CASE(NEG)
                        v = pop();
                        push(unary_operator_negate(&v));
                        break;
                CASE(ADD)
                        right = pop();
                        left = pop();
                        push(binary_operator_addition(&left, &right));
                        break;
                CASE(SUB)
                        right = pop();
                        left = pop();
                        push(binary_operator_subtraction(&left, &right));
                        break;
                CASE(MUL)
                        right = pop();
                        left = pop();
                        push(binary_operator_multiplication(&left, &right));
                        break;
                CASE(DIV)
                        right = pop();
                        left = pop();
                        push(binary_operator_division(&left, &right));
                        break;
                CASE(MOD)
                        right = pop();
                        left = pop();
                        push(binary_operator_remainder(&left, &right));
                        break;
                CASE(EQ)
                        right = pop();
                        left = pop();
                        push(binary_operator_equality(&left, &right));
                        break;
                CASE(NEQ)
                        right = pop();
                        left = pop();
                        push(binary_operator_equality(&left, &right));
                        --top()->boolean;
                        break;
                CASE(LT)
                        right = pop();
                        left = pop();
                        push(BOOLEAN(value_compare(&left, &right) < 0));
                        break;
                CASE(GT)
                        right = pop();
                        left = pop();
                        push(BOOLEAN(value_compare(&left, &right) > 0));
                        break;
                CASE(LEQ)
                        right = pop();
                        left = pop();
                        push(BOOLEAN(value_compare(&left, &right) <= 0));
                        break;
                CASE(GEQ)
                        right = pop();
                        left = pop();
                        push(BOOLEAN(value_compare(&left, &right) >= 0));
                        break;
                CASE(CMP)
                        right = pop();
                        left = pop();
                        i = value_compare(&left, &right);
                        if (i < 0)
                                push(INTEGER(-1));
                        else if (i > 0)
                                push(INTEGER(1));
                        else
                                push(INTEGER(0));
                        break;
                CASE(GET_TAG)
                        v = pop();
                        if (v.tags == 0)
                                push(NIL);
                        else
                                push(TAG(tags_first(v.tags)));
                        break;
                CASE(LEN)
                        v = pop();
                        push(INTEGER(v.array->count)); // TODO
                        break;
                CASE(PRE_INC)
                        switch (peektarget()->type) {
                        case VALUE_INTEGER: ++peektarget()->integer; break;
                        case VALUE_REAL:    ++peektarget()->real;    break;
                        default:            vm_panic("pre-increment applied to invalid type");
                        }
                        push(*poptarget());
                        break;
                CASE(POST_INC)
                        push(*peektarget());
                        switch (peektarget()->type) {
                        case VALUE_INTEGER: ++peektarget()->integer; break;
                        case VALUE_REAL:    ++peektarget()->real;    break;
                        default:            vm_panic("post-increment applied to invalid type");
                        }
                        poptarget();
                        break;
                CASE(PRE_DEC)
                        switch (peektarget()->type) {
                        case VALUE_INTEGER: --peektarget()->integer; break;
                        case VALUE_REAL:    --peektarget()->real;    break;
                        default:            vm_panic("pre-decrement applied to invalid type");
                        }
                        push(*poptarget());
                        break;
                CASE(POST_DEC)
                        push(*peektarget());
                        switch (peektarget()->type) {
                        case VALUE_INTEGER: --peektarget()->integer; break;
                        case VALUE_REAL:    --peektarget()->real;    break;
                        default:            vm_panic("post-decrement applied to invalid type");
                        }
                        poptarget();
                        break;
                CASE(MUT_ADD)
                        vp = poptarget();
                        if (vp->type == VALUE_ARRAY) {
                                if (top()->type != VALUE_ARRAY)
                                        vm_panic("attempt to add non-array to array");
                                value_array_extend(vp->array, pop().array);
                        } else if (vp->type == VALUE_DICT) {
                                if (top()->type != VALUE_DICT)
                                        vm_panic("attempt to add non-dict to dict");
                                dict_update(vp, 1);
                                pop();
                        } else {
                                v = pop();
                                *vp = binary_operator_addition(vp, &v);
                        }
                        push(*vp);
                        break;
                CASE(MUT_MUL)
                        vp = poptarget();
                        v = pop();
                        *vp = binary_operator_multiplication(vp, &v);
                        push(*vp);
                        break;
                CASE(MUT_DIV)
                        vp = poptarget();
                        v = pop();
                        *vp = binary_operator_division(vp, &v);
                        push(*vp);
                        break;
                CASE(MUT_SUB)
                        vp = poptarget();
                        if (vp->type == VALUE_DICT) {
                                if (top()->type != VALUE_DICT)
                                        vm_panic("attempt to subtract non-dict from dict");
                                dict_subtract(vp, 1);
                                pop();
                        } else {
                                v = pop();
                                *vp = binary_operator_subtraction(vp, &v);
                        }
                        push(*vp);
                        break;
                CASE(DEFINE_TAG)
                {
                        int tag, super, n;
                        READVALUE(tag);
                        READVALUE(super);
                        READVALUE(n);
                        while (n --> 0) {
                                v = pop();
                                if (v.refs != NULL)
                                        NOGC(v.refs);
                                tags_add_method(tag, ip, v);
                                ip += strlen(ip) + 1;
                        }
                        if (super != -1)
                                tags_copy_methods(tag, super);
                        break;
                }
                CASE(DEFINE_CLASS)
                {
                        int class, super, n;
                        READVALUE(class);
                        READVALUE(super);
                        READVALUE(n);
                        while (n --> 0) {
                                v = pop();
                                if (v.refs != NULL)
                                        NOGC(v.refs);
                                class_add_method(class, ip, v);
                                ip += strlen(ip) + 1;
                        }
                        class_set_super(class, super);
                        break;
                }
                CASE(FUNCTION)
                {
                        v.tags = 0;
                        v.type = VALUE_FUNCTION;
                        v.this = NULL;

                        int params;
                        int bound;
                        bool rest;

                        READVALUE(params);
                        READVALUE(bound);
                        READVALUE(rest);

                        v.bound = bound;
                        v.params = params;
                        v.rest = rest;

                        while (*ip != ((char)0xFF))
                                ++ip;
                        ++ip;

                        v.symbols = (int *) ip;
                        ip += bound * sizeof (int);

                        READVALUE(n);
                        v.code = ip;
                        ip += n;

                        READVALUE(n);
                        v.refs = (n == 0) ? NULL : ref_vector_new(n);
                        //LOG("function contains %d reference(s)", n);
                        for (int i = 0; i < n; ++i) {
                                READVALUE(s);
                                READVALUE(off);
                                vars[s]->captured = true;
                                struct reference ref = { .pointer = (uintptr_t) vars[s], .offset = off };
                                //LOG("it refers to symbol %d", (int) s);
                                //LOG("it refers to pointer %p", (void *) ref.pointer);
                                v.refs->refs[i] = ref;
                        }

                        push(v);
                        break;
                }
                CASE(CALL)
                        v = pop();
                        READVALUE(n);
                Call:
                        gc_push(&v);
                        switch (v.type) {
                        case VALUE_FUNCTION:
                                call(&v, NULL, n, false);
                                break;
                        case VALUE_BUILTIN_FUNCTION:
                                v = v.builtin_function(n);
                                stack.count -= n;
                                push(v);
                                break;
                        case VALUE_TAG:
                                if (n == 1) {
                                        top()->tags = tags_push(top()->tags, v.tag);
                                        top()->type |= VALUE_TAGGED;
                                } else {
                                        struct array *items = value_array_new();
                                        vec_reserve(*items, n);
                                        items->count = n;
                                        while (n --> 0)
                                                items->items[n] = pop();
                                        value = ARRAY(items);
                                        value.type |= VALUE_TAGGED;
                                        value.tags = tags_push(value.tags, v.tag);
                                        push(value);
                                }
                                break;
                        case VALUE_CLASS:
                                value = OBJECT(object_new(), v.class);
                                vp = class_method(v.class, "init");
                                if (vp != NULL) {
                                        call(vp, &value, n, true);
                                        pop();
                                } else {
                                        stack.count -= n;
                                }
                                push(value);
                                break;
                        case VALUE_METHOD:
                                call(v.method, v.this, n, false);
                                break;
                        case VALUE_REGEX:
                                if (n != 1)
                                        vm_panic("attempt to apply a regex to an invalid number of values");
                                value = pop();
                                if (value.type != VALUE_STRING)
                                        vm_panic("attempt to apply a regex to a non-string: %s", value_show(&value));
                                push(v);
                                *top() = get_string_method("match!")(&value, 1);
                                break;
                        case VALUE_BUILTIN_METHOD:
                                v = v.builtin_method(v.this, n);
                                stack.count -= n;
                                push(v);
                                break;
                        case VALUE_NIL:
                                stack.count -= n;
                                push(NIL);
                                break;
                        default:
                                vm_panic("attempt to call non-callable value %s", value_show(&v));
                        }
                        gc_pop();
                        break;
                CASE(CALL_METHOD)
                        
                        value = peek();

                        vp = NULL;
                        func = NULL;
                        struct value *self = NULL;

                        char const *method = ip;
                        ip += strlen(ip) + 1;

                        READVALUE(h);
                        READVALUE(n);

                        for (int tags = value.tags; tags != 0; tags = tags_pop(tags)) {
                                vp = tags_lookup_method(tags_first(tags), method, h);
                                if (vp != NULL) {
                                        value.tags = tags_pop(tags);
                                        if (value.tags == 0)
                                                value.type &= ~VALUE_TAGGED;
                                        self = &value;
                                        break;
                                }
                        }

                        /*
                         * If we get here and self is a null pointer, none of the value's tags (if it even had any)
                         * supported the  method call, so we must now see if the inner value itself can handle the method
                         * call.
                         */
                        if (self == NULL) switch (value.type & ~VALUE_TAGGED) {
                        case VALUE_TAG:
                                vp = tags_lookup_method(value.tag, method, h);
                                break;
                        case VALUE_STRING:
                                func = get_string_method(method);
                                break;
                        case VALUE_DICT:
                                func = get_dict_method(method);
                                break;
                        case VALUE_ARRAY:
                                func = get_array_method(method);
                                break;
                        case VALUE_BLOB:
                                func = get_blob_method(method);
                                break;
                        case VALUE_CLASS: /* lol */
                                vp = class_lookup_method(value.class, method, h);
                                break;
                        case VALUE_OBJECT:
                                vp = class_lookup_method(value.class, method, h);
                                if (vp == NULL) {
                                        vp = table_lookup(value.object, method, h);
                                } else {
                                        self = &value;
                                }
                                break;
                        case VALUE_NIL:
                                pop();
                                stack.count -= n;
                                push(NIL);
                                continue;
                        }

                        if (func != NULL) {
                                value.type &= ~VALUE_TAGGED;
                                value.tags = 0;
                                pop();
                                gc_push(&value);
                                v = func(&value, n);
                                gc_pop();
                                stack.count -= n;
                                push(v);
                        } else if (vp != NULL) {
                                if (self != NULL) {
                                        v = METHOD(method, vp, self);
                                } else {
                                        v = *vp;
                                }
                                --stack.count;
                                goto Call;
                        } else {
                                vm_panic("call to non-existent method '%s' on %s", method, value_show(&value));
                        }
                        break;
                CASE(SAVE_STACK_POS)
                        vec_push(sp_stack, stack.count);
                        break;
                CASE(RESTORE_STACK_POS)
                        stack.count = *vec_pop(sp_stack);
                        break;
                CASE(MULTI_RETURN)
                        READVALUE(rc);
                        stack.count -= rc;
                        /* fallthrough */
                CASE(RETURN)
                        ip = *vec_pop(calls);
                        LOG("returning: ip = %p", ip);
                        break;
                CASE(HALT)
                        ip = save;
                        LOG("halting: ip = %p", ip);
                        return;
                }
        }
}

char const *
vm_error(void)
{
        return err_msg;
}

bool
vm_init(int ac, char **av)
{
        vec_init(stack);
        vec_init(calls);
        vec_init(targets);
        vars = NULL;
        symbol_count = 0;

        pcre_malloc = alloc;

        srand(time(NULL));

        compiler_init();

        add_builtins(ac, av);

        char *prelude = compiler_load_prelude();
        if (prelude == NULL) {
                err_msg = compiler_error();
                return false;
        }

        int new_symbol_count = compiler_symbol_count();
        resize(vars, new_symbol_count * sizeof *vars);
        resize(used, new_symbol_count * sizeof *used);
        while (symbol_count < new_symbol_count) {
                used[symbol_count] = false;
                vars[symbol_count++] = NULL;
        }

        if (setjmp(jb) != 0) {
                err_msg = err_buf;
                return false;
        }

        vm_exec(prelude);

        return true;
}

noreturn void
vm_panic(char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        char const *file;
        struct location loc = compiler_get_location(ip, &file);

        int n;
        if (file == NULL)
                n = sprintf(err_buf, "RuntimeError: %d:%d: ", loc.line + 1, loc.col + 1);
        else
                n = sprintf(err_buf, "RuntimeError: %s:%d:%d: ", file, loc.line + 1, loc.col + 1);
        vsnprintf(err_buf + n, sizeof err_buf - n, fmt, ap);

        va_end(ap);

        LOG("VM Error: %s", err_buf);

        longjmp(jb, 1);
}

bool
vm_execute_file(char const *path)
{
        char *source = slurp(path);
        if (source == NULL) {
                err_msg = "failed to read source file";
                return false;
        }

        filename = path;

        bool success = vm_execute(source);
        free(source);

        filename = NULL;

        return success;
}

bool
vm_execute(char const *source)
{
        if (filename == NULL)
                filename = "<interactive>";

        char *code = compiler_compile_source(source, filename);
        if (code == NULL) {
                err_msg = compiler_error();
                LOG("compiler error was: %s", err_msg);
                return false;
        }

        int new_symbol_count = compiler_symbol_count();
        resize(vars, new_symbol_count * sizeof *vars);
        resize(used, new_symbol_count * sizeof *used);
        while (symbol_count < new_symbol_count) {
                //LOG("SETTING %d TO NULL", symbol_count);
                used[symbol_count] = false;
                vars[symbol_count++] = NULL;
        }

        if (setjmp(jb) != 0) {
                gc_clear_root_set();
                stack.count = 0;
                sp_stack.count = 0;
                try_stack.count = 0;
                targets.count = 0;
                err_msg = err_buf;
                return false;
        }

        vm_exec(code);

        return true;
}

void
vm_push(struct value const *v)
{
        push(*v);
}

void
vm_pop(void)
{
        stack.count -= 1;
}

struct value *
vm_get(int i)
{
        return top() - i;
}


struct value
vm_call(struct value const *f, int argc)
{
        struct value r, *init;

        switch (f->type) {
        case VALUE_FUNCTION:
                call(f, NULL, argc, true);
                return pop();
        case VALUE_METHOD:
                call(f->method, f->this, argc, true);
                return pop();
        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(argc);
                stack.count -= argc;
                return r;
        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(f->this, argc);
                stack.count -= argc;
                return r;
        case VALUE_TAG:
                r = pop();
                r.tags = tags_push(r.tags, f->tag);
                r.type |= VALUE_TAGGED;
                return r;
        case VALUE_CLASS:
                r = OBJECT(object_new(), f->class);
                init = class_method(f->class, "init");
                if (init != NULL)
                        call(init, &r, argc, true);
                return r;
        default:
                abort();
        }
}

struct value
vm_eval_function(struct value const *f, ...)
{
        int argc;
        va_list ap;
        struct value r;
        struct value const *v;

        va_start(ap, f);
        argc = 0;

        while ((v = va_arg(ap, struct value const *)) != NULL) {
                push(*v);
                argc += 1;
        }

        va_end(ap);

        switch (f->type) {
        case VALUE_FUNCTION:
                call(f, NULL, argc, true);
                return pop();
        case VALUE_METHOD:
                call(f->method, f->this, argc, true);
                return pop();
        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(argc);
                stack.count -= argc;
                return r;
        default:
                abort();
        }
}

void
vm_mark(void)
{
        for (int i = 0; i < symbol_count; ++i) if (used[i]) {
                for (struct variable *v = vars[i]; v != NULL; v = v->next) {
                        value_mark(&v->value);
                }
        }

        for (int i = 0; i < stack.count; ++i)
                value_mark(&stack.items[i]);

        for (int i = 0; i < targets.count; ++i)
                value_mark(targets.items[i].t);
}

TEST(let)
{
        char const *source = "let a = 5;";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        claim(vars[0 + builtin_count]->value.integer == 5);
}

TEST(loop)
{
        char const *source = "let a = 0; for (let i = 0; i < 10; i = i + 1) a = a + 2;";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        LOG("value is %d", (int) vars[0 + builtin_count]->value.integer);
        claim(vars[0 + builtin_count]->value.integer == 20);
}

TEST(func)
{
        char const *source = "let a = 0; let f = function () { a = a + 1; }; f(); f();";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        LOG("value is %d", (int) vars[0 + builtin_count]->value.integer);
        claim(vars[0 + builtin_count]->value.integer == 2);
}

TEST(stress) // OFF
{
        char const *source = "let n = 0; for (let i = 0; i < 1000000; i = i + 1) { n = n + 1; }";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        LOG("value is %d", (int) vars[0 + builtin_count]->value.integer);
        claim(vars[0 + builtin_count]->value.integer == 1000000);
}

TEST(stress2) // OFF
{
        char const *source = "let n = 0; for (let i = 0; i < 1000000; i = i + 1) { n = n + (function () return 1;)(); }";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        LOG("value is %d", (int) vars[0 + builtin_count]->value.integer);
        claim(vars[0 + builtin_count]->value.integer == 1000000);
}

TEST(array)
{
        char const *source = "let a = [1, 2 + 2, 16];";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_ARRAY);
        claim(vars[0 + builtin_count]->value.array->count == 3);
        claim(vars[0 + builtin_count]->value.array->items[0].type == VALUE_INTEGER);
        claim(vars[0 + builtin_count]->value.array->items[1].type == VALUE_INTEGER);
        claim(vars[0 + builtin_count]->value.array->items[2].type == VALUE_INTEGER);
        claim(vars[0 + builtin_count]->value.array->items[0].integer == 1);
        claim(vars[0 + builtin_count]->value.array->items[1].integer == 4);
        claim(vars[0 + builtin_count]->value.array->items[2].integer == 16);
}

TEST(object)
{
        char const *source = "let o = {'test': 'hello'};";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_DICT);
        struct value *v = dict_get_member(vars[0 + builtin_count]->value.dict, "test");
        claim(v != NULL);
        claim(strcmp(v->string, "hello") == 0);
}

TEST(member_access)
{
        char const *source = "let o = {'test': 'hello'}; let h = o.test;";

        vm_init(0, NULL);

        if (!vm_execute(source))
                printf("error: %s\n", vm_error());

        claim(vars[1 + builtin_count]->value.type == VALUE_STRING);
        claim(strcmp(vars[1 + builtin_count]->value.string, "hello") == 0);
}

TEST(subscript)
{
        char const *source = "let o = {'test': 'hello'}; let h = o['test'];";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[1 + builtin_count]->value.type == VALUE_STRING);
        claim(strcmp(vars[1 + builtin_count]->value.string, "hello") == 0);
}

TEST(array_lvalue)
{
        char const *source = "let [a, [b, c]] = [4, [10, 16]];";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        claim(vars[0 + builtin_count]->value.integer == 4);

        claim(vars[1 + builtin_count]->value.type == VALUE_INTEGER);
        claim(vars[1 + builtin_count]->value.integer == 10);

        claim(vars[2 + builtin_count]->value.type == VALUE_INTEGER);
        claim(vars[2 + builtin_count]->value.integer == 16);
}

TEST(array_subscript)
{
        char const *source = "let a = [4, 5, 6]; a[0] = 42; let b = a[0];";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[1 + builtin_count]->value.type == VALUE_INTEGER);
        claim(vars[1 + builtin_count]->value.integer == 42);
}

TEST(func_with_args)
{
        char const *source = "let a = 0; let f = function (k) { return k + 10; }; a = f(32);";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        claim(vars[0 + builtin_count]->value.integer == 42);
}

TEST(if_else)
{
        char const *source = "let [a, b] = [nil, nil]; if (false) { a = 48; } else { a = 42; } if (true) { b = 42; } else { b = 98; }";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        claim(vars[0 + builtin_count]->value.integer == 42);

        claim(vars[1 + builtin_count]->value.type == VALUE_INTEGER);
        claim(vars[1 + builtin_count]->value.integer == 42);
}

TEST(recursive_func)
{
        char const *source = "let a = 0; function f(k) if (k == 1) return 1; else return k * f(k - 1); a = f(5);";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_INTEGER);
        LOG("a = %d", (int) vars[0 + builtin_count]->value.integer);
        claim(vars[0 + builtin_count]->value.integer == 120);
}

TEST(method_call)
{
        char const *source = "let o = nil; o = {'name': 'foobar', 'getName': function () { return o.name; }}; o = o.getName();";

        vm_init(0, NULL);

        vm_execute(source);

        claim(vars[0 + builtin_count]->value.type == VALUE_STRING);
        claim(strcmp(vars[0 + builtin_count]->value.string, "foobar") == 0);
}

TEST(print)
{
        vm_init(0, NULL);
        vm_execute("print(45);");
}


TEST(each)
{
        vm_init(0, NULL);
        claim(vm_execute("let o = { 'name': 'Bob', 'age':  19 };"));
        claim(vm_execute("for (k in @o) { print(k); print(o[k]); print('---'); }"));
}

TEST(bench)
{
        vm_init(0, NULL);
        vm_execute("for (let i = 0; i < 1000; i = i + 1) { let [a, b, c] = [{}, {}, {}]; }");
}

TEST(factorial)
{
        vm_init(0, NULL);

        vm_execute("let f = function (k) if (k == 1) return 1; else return k * f(k - 1);;");
        vm_execute("f(5);");
}

TEST(match)
{
        vm_init(0, NULL);

        vm_execute("match 4 { 4 | false => print('oh no!');, 5 => print('oh dear!');, 4 => print('Yes!'); }");
}

TEST(tagmatch)
{

        vm_init(0, NULL);

        vm_execute("tag Add; match Add(4) { Add(k) => print(k); }");
}

TEST(matchrest)
{
        vm_init(0, NULL);
        vm_execute("match [4, 5, 6] { [4, *xs] => print(xs); }");
}
