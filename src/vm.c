#include <time.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdbool.h>
#include <setjmp.h>
#include <stdarg.h>
#include <errno.h>
#include <stdnoreturn.h>

#include <pcre.h>
#include <curl/curl.h>

#include <poll.h>
#include <fcntl.h>
#include <unistd.h>
#include <signal.h>
#include <dirent.h>

#include <sys/types.h>
#include <sys/epoll.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <netdb.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <netdb.h>
#include <netinet/ip.h>

#include "cffi.h"
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
#include "curl.h"
#include "sqlite.h"

#define TY_LOG_VERBOSE 1

#define READVALUE(s) (memcpy(&s, ip, sizeof s), (ip += sizeof s))

#if defined(TY_LOG_VERBOSE) && !defined(TY_NO_LOG)
  #define CASE(i) case INSTR_ ## i: fname = compiler_get_location(ip, &loc, &loc); LOG("%s:%d:%d: " #i, fname, loc.line + 1, loc.col + 1);
#else
  #define CASE(i) case INSTR_ ## i:
#endif

#define inline __attribute__((always_inline)) inline

static char halt = INSTR_HALT;
static char next_fix[] = { INSTR_NONE_IF_NIL, INSTR_RETURN_PRESERVE_CTX };
static char iter_fix[] = { INSTR_SENTINEL, INSTR_RETURN_PRESERVE_CTX };

static jmp_buf jb;

struct try {
        jmp_buf jb;
        int sp;
        int gc;
        int cs;
        int ts;
        int ctxs;
        char *catch;
        char *finally;
        char *end;
        bool executing;
};

struct target {
        struct value *t;
        void *gc;
};

static vec(struct value) Globals;

struct sigfn {
        int sig;
        struct value f;
};

typedef struct Frame {
        size_t fp;
        struct value f;
        char const *ip;
} Frame;

#define FRAME(n, fn, from) ((Frame){ .fp = (n), .f = (fn), .ip = (from) })

typedef vec(struct value) ValueStack;
typedef vec(Frame) FrameStack;
typedef vec(char *) CallStack;
typedef vec(size_t) SPStack;
typedef vec(struct target) TargetStack;

typedef struct ctx {
        ValueStack vs;
        char *ip;
} Context;

static vec(struct sigfn) sigfns;
static vec(struct value) stack;
static vec(char *) calls;
static vec(Frame) frames;
static vec(size_t) sp_stack;
static vec(struct target) targets;
static vec(struct try) try_stack;
static char *ip;

static char const *filename;

static char const *Error;

static struct {
        char const *module;
        char const *name;
        struct value value;
} builtins[] = {
#include "builtins.h"
};

static int builtin_count = sizeof builtins / sizeof builtins[0];

pcre_jit_stack *JITStack = NULL;

static void
vm_exec(char *code);

/*
 * This relies on no other symbols being introduced to the compiler
 * up until the point that this is called. i.e., it assumes that the
 * first built-in function should have symbol 0. I think this is ok.
 */
static void
add_builtins(int ac, char **av)
{
        for (int i = 0; i < builtin_count; ++i) {
                compiler_introduce_symbol(builtins[i].module, builtins[i].name);
                vec_push(Globals, builtins[i].value);
        }

        struct array *args = value_array_new();
        NOGC(args);

        for (int i = 1; i < ac; ++i)
                value_array_push(args, STRING_NOGC(av[i], strlen(av[i])));

        compiler_introduce_symbol("os", "args");
        vec_push(Globals, ARRAY(args));

        /* Add this here because SIGRTMIN doesn't expand to a constant */
        compiler_introduce_symbol("os", "SIGRTMIN");
        vec_push(Globals, INTEGER(SIGRTMIN));
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

        for (int i = 0; i < n; ++i) {
                compiler_introduce_symbol(name, mod[i].name);
                vec_push(Globals, mod[i].value);
        }
}

inline static struct value *
top(void)
{
        return &stack.items[stack.count] - 1;
}

static void
print_stack(int n)
{
#ifndef TY_NO_LOG
        LOG("STACK: (%zu)", stack.count);
        for (int i = 0; i < n && i < stack.count; ++i) {
                if (frames.count > 0 && stack.count - (i + 1) == vec_last(frames)->fp) {
                        LOG(" -->  %s", value_show(top() - i));
                } else {
                        LOG("      %s", value_show(top() - i));
                }
        }
#endif
}

inline static struct value
pop(void)
{
        LOG("POP: %s", value_show(top()));
        struct value v = *vec_pop(stack);
        print_stack(15);
        return v;
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
        print_stack(10);
}

inline static struct value *
local(int i)
{
        return &stack.items[vec_last(frames)->fp + i];
}

inline static struct value *
poptarget(void)
{
        struct target t = *vec_pop(targets);
        if (t.gc != NULL) OKGC(t.gc);
        LOG("Popping Target: %p", (void *)t.t);
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
        LOG("TARGETS: (%zu)", targets.count);
        for (int i = 0; i < targets.count; ++i) {
                LOG("\t%d: %p", i + 1, (void *)targets.items[i].t);
        }
}

inline static void
call(struct value const *f, struct value const *self, int n, int nkw, bool exec)
{
        int bound = f->info[3];
        int np = f->info[4];
        bool rest = f->info[5] & 2;
        bool has_kwargs = f->info[5] & 1;
        int class = f->info[6];
        char *code = code_of(f);
        int argc = n;

        struct value kwargs = (nkw > 0) ? pop() : NIL;

        /*
         * This is the index of the beginning of the stack frame for this call to f.
         */
        int fp = stack.count - n;

        /*
         * Default missing arguments to NIL and make space for all of this function's local variables.
         */
        while (n < bound) {
                push(NIL);
                n += 1;
        }

        /*
         * If the function was declared with the form f(..., *extra) then we
         * create an array and add any extra arguments to it.
         */
        if (rest) {
                struct array *extra = value_array_new();
                NOGC(extra);

                for (int i = np - 1 - has_kwargs; i < argc; ++i) {
                        value_array_push(extra, stack.items[fp + i]);
                        stack.items[fp + i] = NIL;
                }

                stack.items[fp + np - 1 - has_kwargs] = ARRAY(extra);
                OKGC(extra);
        }

        if (has_kwargs) {
                stack.items[fp + np - 1] = (nkw > 0) ? kwargs : DICT(dict_new());
        }

        /*
         * Throw away extra arguments.
         */
        while (n > bound) {
                pop();
                n -= 1;
        }

        /*
         * Fill in 'self' as an implicit additional parameter.
         */
        if (self != NULL && class != -1) {
                LOG("setting self = %s", value_show(self));
                stack.items[fp + np] = *self;
        }

        vec_push(frames, FRAME(fp, *f, ip));

        /* Fill in keyword args (overwriting positional args) */
        if (kwargs.type != VALUE_NIL) {
                char const *name = (char const *)(f->info + 7);
                for (int i = 0; i < np; ++i) {
                        name += strlen(name) + 1;
                        struct value *arg = dict_get_member(kwargs.dict, name);
                        if (arg != NULL) {
                                *local(i) = *arg;
                        }
                }
        }

        LOG("Calling %s with %d args, bound = %d, self = %s, env size = %d", value_show(f), argc, bound, self ? value_show(self) : "none", f->info[2]);
        print_stack(max(bound + 2, 5));

        if (exec) {
                vec_push(calls, &halt);
                gc_push(f);
                vm_exec(code);
                gc_pop();
        } else {
                vec_push(calls, ip);
                ip = code;
        }
}

inline static void
call_co(struct value *v, int n)
{
        if (v->gen->ip != code_of(&v->gen->f)) {
                if (n == 0) {
                        vec_push(v->gen->frame, NIL);
                } else {
                        vec_push_n(v->gen->frame, top() - (n - 1), n);
                        stack.count -= n;
                }
        }

        push(*v);

        call(&v->gen->f, NULL, 0, 0, false);
        stack.count = vec_last(frames)->fp;

        for (int i = 0; i < v->gen->frame.count; ++i) {
                push(v->gen->frame.items[i]);
        }

        ip = v->gen->ip;
}

void
vm_del_sigfn(int sig)
{
        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        struct sigfn t = *vec_last(sigfns);
                        *vec_last(sigfns) = sigfns.items[i];
                        sigfns.items[i] = t;
                        vec_pop(sigfns);
                        return;
                }
        }
}

void
vm_set_sigfn(int sig, struct value const *f)
{
        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        sigfns.items[i].f = *f;
                        return;
                }
        }

        vec_push(sigfns, ((struct sigfn){ .sig = sig, .f = *f }));
}

struct value
vm_get_sigfn(int sig)
{
        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        return sigfns.items[i].f;
                }
        }

        return NIL;
}

void
vm_do_signal(int sig, siginfo_t *info, void *ctx)
{
        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        switch (sig) {
                        case SIGIO:
                                push(INTEGER(info->si_fd));
                                call(&sigfns.items[i].f, NULL, 1, 0, true);
                                break;
                        default:
                                call(&sigfns.items[i].f, NULL, 0, 0, true);
                        }
                        return;
                }
        }
}

static void
vm_exec(char *code)
{
        char *save = ip;
        ip = code;

        uintptr_t s, off;
        intmax_t k;
        bool b = false, tco = false;
        float f;
        int n, nkw = 0, i, j, tag, rc = 0;
        unsigned long h;

        struct value left, right, v, key, value, container, subscript, *vp;
        char *str;
        char const *method, *member;

        struct value (*func)(struct value *, int);

#ifdef TY_LOG_VERBOSE
        struct location loc;
        char const *fname;
#endif

        for (;;) {
        NextInstruction:
                switch ((unsigned char)*ip++) {
                CASE(NOP)
                        continue;
                CASE(LOAD_LOCAL)
                        READVALUE(n);
                        LOG("Loading %d", n);
                        push(*local(n));
                        break;
                CASE(LOAD_REF)
                        READVALUE(n);
                        vp = local(n);
                        if (vp->type == VALUE_REF) {
                                push(*(struct value *)vp->ptr);
                        } else {
                                push(*vp);
                        }
                        break;
                CASE(LOAD_CAPTURED)
                        READVALUE(n);
                        LOG("Loading capture %d of %s", n, value_show(&vec_last(frames)->f));
                        push(*vec_last(frames)->f.env[n]);
                        break;
                CASE(LOAD_GLOBAL)
                        READVALUE(n);
                        LOG("Loading global: %d", n);
                        push(Globals.items[n]);
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
                CASE(JUMP_IF_NIL)
                        READVALUE(n);
                        v = pop();
                        if (v.type == VALUE_NIL) {
                                ip += n;
                        }
                        break;
                CASE(TARGET_GLOBAL)
                TargetGlobal:
                        READVALUE(n);
                        LOG("Global: %d", (int)n);
                        while (Globals.count <= n)
                                vec_push(Globals, NIL);
                        pushtarget(&Globals.items[n], NULL);
                        break;
                CASE(TARGET_LOCAL)
                        if (frames.count == 0)
                                goto TargetGlobal;
                        READVALUE(n);
                        pushtarget(local(n), NULL);
                        break;
                CASE(TARGET_REF)
                        READVALUE(n);
                        vp = local(n);
                        if (vp->type == VALUE_REF) {
                                pushtarget((struct value *)vp->ptr, NULL);
                        } else {
                                pushtarget(vp, NULL);
                        }
                        break;
                CASE(TARGET_CAPTURED)
                        READVALUE(n);
                        pushtarget(vec_last(frames)->f.env[n], NULL);
                        break;
                CASE(TARGET_MEMBER)
                        v = pop();
                        if (v.type != VALUE_OBJECT)
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
                        subscript = top()[0];
                        container = top()[-1];

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

                        pop();
                        pop();

                        break;
                CASE(ASSIGN)
                        *poptarget() = peek();
                        break;
                CASE(MAYBE_ASSIGN)
                        vp = poptarget();
                        if (vp->type == VALUE_NIL)
                                *vp = peek();
                        break;
                CASE(TAG_PUSH)
                        READVALUE(tag);
                        top()->tags = tags_push(top()->tags, tag);
                        top()->type |= VALUE_TAGGED;
                        break;
                CASE(ARRAY_REST)
                        READVALUE(i);
                        READVALUE(n);
                        if (top()->type != VALUE_ARRAY) {
                                LOG("cannot do rest: top is not an array");
                                ip += n;
                        } else {
                                //TODO: fix this
                                //vec_push_n(*vars[s]->value.array, top()->array->items + i, top()->array->count - i);
                                struct array *rest = value_array_new();
                                vec_push_n(*rest, top()->array->items + i, top()->array->count - i);
                                *poptarget() = ARRAY(rest);
                        }
                        break;
                CASE(TUPLE_REST)
                        READVALUE(i);
                        READVALUE(n);
                        if (top()->type != VALUE_TUPLE) {
                                ip += n;
                        } else {
                                int count = top()->count - i;
                                struct value *rest = gc_alloc_object(sizeof (struct value[count]), GC_TUPLE);
                                memcpy(rest, top()->items + i, count * sizeof (struct value));
                                *poptarget() = TUPLE(rest, NULL, count);
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
                CASE(BAD_CALL)
                        v = pop();
                        str = ip;
                        ip += strlen(ip) + 1;
                        vm_panic(
                                "constraint on %s%s%s%s%s violated in call to %s%s%s%s%s: %s%s%s = %s%s%s",
                                TERM(34),
                                TERM(1),
                                ip,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                str,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                ip,
                                value_show(&v),
                                TERM(22),
                                TERM(39)
                        );
                        break;
                CASE(BAD_ASSIGN)
                        v = pop();
                        str = ip;
                        vm_panic(
                                "constraint on %s%s%s%s%s violated in assignment: %s%s%s = %s%s%s",
                                TERM(34),
                                TERM(1),
                                ip,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                ip,
                                value_show(&v),
                                TERM(22),
                                TERM(39)
                        );
                        break;
                CASE(THROW)
Throw:
                        if (try_stack.count == 0) {
                                vm_panic("uncaught exception: %s%s%s", TERM(31), value_show(top()), TERM(39));
                        }

                        struct try *t = vec_last(try_stack);

                        if (t->executing) {
                                vm_panic(
                                        "an exception was thrown while handling another exception: %s%s%s",
                                        TERM(31), value_show(top()), TERM(39)
                                );
                        } else {
                                t->executing = true;
                        }

                        v = pop();
                        stack.count = t->sp;
                        push(SENTINEL);
                        push(v);

                        targets.count = t->ts;
                        calls.count = t->cs;
                        ip = t->catch;
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
                        frames.count = vec_last(try_stack)->ctxs;
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
                        t.ctxs = targets.count;
                        t.executing = false;
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
                CASE(ENSURE_LEN_TUPLE)
                        READVALUE(n);
                        b = top()->count == n;
                        READVALUE(n);
                        if (!b)
                                ip += n;
                        break;
                CASE(ENSURE_EQUALS_VAR)
                        v = pop();
                        READVALUE(n);
                        if (!value_test_equality(top(), &v))
                                ip += n;
                        break;
                CASE(TRY_ASSIGN_NON_NIL)
                        READVALUE(n);
                        vp = poptarget();
                        if (top()->type == VALUE_NIL)
                                ip += n;
                        else
                                *vp = peek();
                        break;
                CASE(TRY_REGEX)
                        READVALUE(s);
                        READVALUE(n);
                        v = REGEX((struct regex const *) s);
                        value = value_apply_callable(&v, top());
                        vp = poptarget();
                        if (value.type == VALUE_NIL) {
                                ip += n;
                        } else if (value.type == VALUE_STRING) {
                                *vp = value;
                        } else {
                                for (int i = 0; i < value.array->count; ++i) {
                                        vp[i] = value.array->items[i];
                                }
                        }
                        break;
                CASE(ENSURE_DICT)
                        READVALUE(n);
                        if (top()->type != VALUE_DICT) {
                                ip += n;
                        }
                        break;
                CASE(ENSURE_CONTAINS)
                        READVALUE(n);
                        v = pop();
                        if (!dict_has_value(top()->dict, &v)) {
                                ip += n;
                        }
                        break;
                CASE(ENSURE_SAME_KEYS)
                        READVALUE(n);
                        v = pop();
                        if (!dict_same_keys(top()->dict, v.dict)) {
                                ip += n;
                        }
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
                CASE(TRY_INDEX_TUPLE)
                        READVALUE(i);
                        READVALUE(n);
                        if (top()->type != VALUE_TUPLE || top()->count <= i) {
                                ip += n;
                        } else {
                                push(top()->items[i]);
                        }
                        break;
                CASE(TRY_TUPLE_MEMBER)
                        str = ip;
                        ip += strlen(str) + 1;
                        READVALUE(n);

                        printf("Looking for '%s'\n", str);

                        if (top()->type != VALUE_TUPLE || top()->names == NULL) {
                                ip += n;
                                break;
                        }

                        for (int i = 0; i < top()->count; ++i) {
                                if (top()->names[i] != NULL && strcmp(top()->names[i], str) == 0) {
                                        printf("Found it: %s\n", value_show(top()->items + i));
                                        push(top()->items[i]);
                                        goto NextInstruction;
                                }
                        }

                        ip += n;

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
                CASE(UNPOP)
                        stack.count += 1;
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
                        v = REGEX((struct regex const *) s);
                        push(v);
                        break;
                CASE(ARRAY)
                        v = ARRAY(value_array_new());
                        n = stack.count - *vec_pop(sp_stack);

                        NOGC(v.array);

                        vec_reserve(*v.array, n);

                        memcpy(
                                v.array->items,
                                stack.items + stack.count - n,
                                sizeof (struct value [n])
                        );
                        v.array->count = n;

                        stack.count -= n;

                        push(v);
                        OKGC(v.array);

                        break;
                CASE(TUPLE)
                        n = stack.count - *vec_pop(sp_stack);

                        if (n == 0) {
                                push(TUPLE(NULL, NULL, 0));
                                break;
                        }

                        vp = gc_alloc_object(sizeof (struct value[n]), GC_TUPLE);

                        memcpy(
                                vp,
                                stack.items + stack.count - n,
                                sizeof (struct value [n])
                        );

                        NOGC(vp);

                        v = TUPLE(vp, NULL, n);

                        for (int i = 0; i < n; ++i, ip += strlen(ip) + 1) {
                                if (ip[0] == 0) {
                                        continue;
                                }

                                if (v.names == NULL) {
                                        v.names = gc_alloc_object(sizeof (char *[n]), GC_TUPLE);
                                        for (int i = 0; i < n; ++i) {
                                                v.names[i] = NULL;
                                        }
                                }

                                v.names[i] = ip;
                        }

                        stack.count -= n;
                        push(v);

                        OKGC(vp);

                        break;
                CASE(DICT)
                        v = DICT(dict_new());
                        NOGC(v.dict);

                        n = (stack.count - *vec_pop(sp_stack)) / 2;
                        for (i = 0; i < n; ++i) {
                                value = top()[0];
                                key = top()[-1];
                                dict_put_value(v.dict, key, value);
                                pop();
                                pop();
                        }

                        OKGC(v.dict);
                        push(v);
                        break;
                CASE(DICT_DEFAULT)
                        v = pop();
                        top()->dict->dflt = v;
                        break;
                CASE(SELF)
                        if (frames.count == 0) {
                        } else {
                                push(NIL);
                        }
                        break;
                CASE(NIL)
                        push(NIL);
                        break;
                CASE(TO_STRING)
                        str = ip;
                        n = strlen(str);
                        ip += n + 1;
						if (top()->type == VALUE_PTR) {
							char *s = value_show(top());
							pop();
							push(STRING_NOGC(s, strlen(s)));
							break;
						} else if (n > 0) {
                                v = pop();
                                push(STRING_NOGC(str, n));
                                push(v);
                                n = 1;
                                method = "__fmt__";
                        } else {
                                n = 0;
                                method = "__str__";
                        }
                        b = false;
                        h = strhash(method);
                        goto CallMethod;
                CASE(YIELD)
                        n = vec_last(frames)->fp;
                        v.gen = stack.items[n - 1].gen;
                        v.gen->ip = ip;
                        v.gen->frame.count = 0;
                        vec_push_n(v.gen->frame, stack.items + n, stack.count - n - 1);
                        stack.items[n - 1] = peek();
                        stack.count = n;
                        vec_pop(frames);
                        ip = *vec_pop(calls);
                        break;
                CASE(MAKE_GENERATOR)
                        v.type = VALUE_GENERATOR;
                        v.tags = 0;
                        v.gen = gc_alloc_object(sizeof *v.gen, GC_GENERATOR);
                        NOGC(v.gen);
                        v.gen->ip = ip;
                        v.gen->f = vec_last(frames)->f;
                        n = stack.count - vec_last(frames)->fp;
                        vec_init(v.gen->frame);
                        vec_push_n(v.gen->frame, stack.items + stack.count - n, n);
                        push(v);
                        OKGC(v.gen);
                        goto Return;
                CASE(FUCK)
                CASE(FUCK2)
                CASE(FUCK3)
                        break;
                CASE(GET_NEXT)
                        v = top()[-1];
                        i = top()[-2].i++;
                        //LOG("GET_NEXT: v = %s\n", value_show(&v));
                        //LOG("GET_NEXT: i = %d\n", i);
                        print_stack(10);
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
                                while (off < v.dict->size && v.dict->keys[off].type == 0) {
                                        off += 1;
                                }
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
                                        push(INTEGER(i));
                                        vec_push(calls, ip);
                                        call(vp, &v, 1, 0, false);
                                        *vec_last(calls) = next_fix;
                                } else if ((vp = class_method(v.class, "__iter__")) != NULL) {
                                        pop();
                                        pop();
                                        --top()->i;
                                        /* Have to repeat this instruction */
                                        vec_push(calls, ip - 1);
                                        call(vp, &v, 0, 0, false);
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
                        case VALUE_GENERATOR:
                                vec_push(calls, ip);
                                call_co(&v, 0);
                                *vec_last(calls) = next_fix;
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
                        //if (top()->type == VALUE_NIL)
                                //*top() = NONE;
                // Once iterators are fixed:
                        if (top()->type == VALUE_TAG && top()->tag == TAG_NONE) {
                                *top() = NONE;
                        } else if (top()->tags != 0 && tags_first(top()->tags) == TAG_SOME) {
                                LOG("Dumping in a tag pop: %s", value_show(top()));
                                top()->tags = tags_pop(top()->tags);
                                if (top()->tags == 0) {
                                        top()->type &= ~VALUE_TAGGED;
                                }
                        } else {
                                vm_panic("iterator returned invalid type. expected None or Some(x) but got %s", value_show(top()));
                        }
                        break;
                CASE(CLEAR_RC)
                        rc = 0;
                        break;
                CASE(GET_EXTRA)
                        LOG("GETTING %d EXTRA", rc);
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
                CASE(SWAP)
                        v = top()[-1];
                        top()[-1] = top()[0];
                        top()[0] = v;
                        break;
                CASE(REVERSE)
                        READVALUE(n);
                        for (--n, i = 0; i < n; ++i, --n) {
                                v = top()[-i];
                                top()[-i] = top()[-n];
                                top()[-n] = v;
                        }
                        break;
                CASE(MULTI_ASSIGN)
                        print_stack(5);
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
                CASE(MAYBE_MULTI)
                        READVALUE(n);
                        for (i = 0, vp = top(); pop().type != VALUE_SENTINEL; ++i)
                                ;
                        for (int j = targets.count - n; n > 0; --n, poptarget()) {
                                if (i > 0) {
                                        if (targets.items[j++].t->type == VALUE_NIL)
                                                *targets.items[j - 1].t = vp[-(--i)];
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
                CASE(PUSH_ARRAY_ELEM)
                        READVALUE(n);
                        if (top()->type != VALUE_ARRAY) {
                                vm_panic("attempt to destructure non-array as array in assignment");
                        }
                        if (n >= top()->array->count) {
                                vm_panic("elment index out of range in destructuring assignment");
                        }
                        push(top()->array->items[n]);
                        break;
                CASE(PUSH_TUPLE_ELEM)
                        READVALUE(n);
                        if (top()->type != VALUE_TUPLE) {
                                vm_panic("attempt to destructure non-tuple as tuple in assignment");
                        }
                        if (n >= top()->count) {
                                vm_panic("elment index out of range in destructuring assignment");
                        }
                        push(top()->items[n]);
                        break;
                CASE(PUSH_TUPLE_MEMBER)
                        member = ip;
                        ip += strlen(member) + 1;

                        v = peek();

                        if (v.type != VALUE_TUPLE || v.names == NULL) {
                                goto BadTupleMember;
                        }

                        for (int i = 0; i < v.count; ++i) {
                                if (v.names[i] != NULL && strcmp(v.names[i], member) == 0) {
                                        push(v.items[i]);
                                        goto NextInstruction;
                                }
                        }

                        goto BadTupleMember;
                CASE(PUSH_ALL)
                        v = pop();
                        gc_push(&v);
                        for (int i = 0; i < v.array->count; ++i) {
                                push(v.array->items[i]);
                        }
                        gc_pop();
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
                                if (stack.items[i].bytes > 0) {
                                        memcpy(str + k, stack.items[i].string, stack.items[i].bytes);
                                        k += stack.items[i].bytes;
                                }
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
                        NOGC(v.object);
                        push(left);
                        push(right);
                        call(vp, &v, 2, 0, true);
                        pop();
                        push(v);
                        OKGC(v.object);
                        break;
                CASE(INCRANGE)
                        right = pop();
                        left = pop();

                        i = class_lookup("InclusiveRange");
                        if (i == -1 || (vp = class_method(i, "init")) == NULL) {
                                vm_panic("failed to load InclusiveRange class. was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(), i);
                        NOGC(v.object);
                        push(left);
                        push(right);
                        call(vp, &v, 2, 0, true);
                        pop();
                        push(v);
                        OKGC(v.object);
                        break;
                CASE(TRY_MEMBER_ACCESS)
                CASE(MEMBER_ACCESS)
                        v = pop();

                        b = ip[-1] == INSTR_TRY_MEMBER_ACCESS;

                        member = ip;
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
                        case VALUE_TUPLE:
                                if (v.names == NULL) {
                                        goto BadTupleMember;
                                }
                                for (int i = 0; i < v.count; ++i) {
                                        if (v.names[i] != NULL && strcmp(v.names[i], member) == 0) {
                                                push(v.items[i]);
                                                goto NextInstruction;
                                        }
                                }
                        BadTupleMember:
                                if (b) {
                                        // (1, 2).?z
                                        push(NIL);
                                        break;
                                }
                                vm_panic(
                                        "attmpt to access non-existent field %s'%s'%s of %s%s%s",
                                        TERM(34),
                                        member,
                                        TERM(39),
                                        TERM(97),
                                        value_show(&v),
                                        TERM(39)
                                );
                        case VALUE_DICT:
                                func = get_dict_method(member);
                                if (func == NULL) {
                                        n = CLASS_DICT;
                                        goto ClassLookup;
                                }
                                v.type = VALUE_ARRAY;
                                v.tags = 0;
                                this = gc_alloc_object(sizeof *this, GC_VALUE);
                                *this = v;
                                push(BUILTIN_METHOD(member, func, this));
                                break;
                        case VALUE_ARRAY:
                                func = get_array_method(member);
                                if (func == NULL) {
                                        n = CLASS_ARRAY;
                                        goto ClassLookup;
                                }
                                v.type = VALUE_ARRAY;
                                v.tags = 0;
                                this = gc_alloc_object(sizeof *this, GC_VALUE);
                                *this = v;
                                push(BUILTIN_METHOD(member, func, this));
                                break;
                        case VALUE_STRING:
                                func = get_string_method(member);
                                if (func == NULL) {
                                        n = CLASS_STRING;
                                        goto ClassLookup;
                                }
                                v.type = VALUE_STRING;
                                v.tags = 0;
                                this = gc_alloc_object(sizeof *this, GC_VALUE);
                                *this = v;
                                push(BUILTIN_METHOD(member, func, this));
                                break;
                        case VALUE_BLOB:
                                func = get_blob_method(member);
                                if (func == NULL) {
                                        n = CLASS_BLOB;
                                        goto ClassLookup;
                                }
                                v.type = VALUE_BLOB;
                                v.tags = 0;
                                this = gc_alloc_object(sizeof *this, GC_VALUE);
                                *this = v;
                                push(BUILTIN_METHOD(member, func, this));
                                break;
                        case VALUE_INTEGER:
                                n = CLASS_INT;
                                goto ClassLookup;
                        case VALUE_REAL:
                                n = CLASS_FLOAT;
                                goto ClassLookup;
                        case VALUE_BOOLEAN:
                                n = CLASS_BOOL;
                                goto ClassLookup;
                        case VALUE_FUNCTION:
                        case VALUE_METHOD:
                        case VALUE_BUILTIN_FUNCTION:
                        case VALUE_BUILTIN_METHOD:
                                n = CLASS_FUNCTION;
                                goto ClassLookup;
                        case VALUE_CLASS:
                                vp = class_lookup_method(v.class, member, h);
                                if (vp == NULL) {
                                        n = CLASS_CLASS;
                                        goto ClassLookup;
                                } else {
                                        push(*vp);
                                }
                                break;
                        case VALUE_OBJECT:
                                vp = table_lookup(v.object, member, h);
                                if (vp != NULL) {
                                        push(*vp);
                                        break;
                                }
                                n = v.class;
ClassLookup:
                                vp = class_lookup_method(n, member, h);
                                if (vp != NULL) {
                                        this = gc_alloc_object(sizeof *this, GC_VALUE);
                                        *this = v;
                                        push(METHOD(member, vp, this));
                                        break;
                                }
                                if (b) {
                                        push(NIL);
                                } else {
                                        vm_panic(
                                                "attempt to access non-existent member %s'%s'%s of %s%s%s",
                                                TERM(34),
                                                member,
                                                TERM(39),
                                                TERM(97),
                                                value_show(&v),
                                                TERM(39)
                                        );
                                }
                                break;
                        case VALUE_TAG:
                                vp = tags_lookup_method(v.tag, member, h);
                                push(vp == NULL ? NIL : *vp);
                                break;
                        default:
                                if (b)
                                        push(NIL);
                                else
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
                                                call(vp, &subscript, 0, 0, true);
                                                subscript = pop();
                                                goto ObjectSubscript;
                                        }
                                        struct array *a = value_array_new();
                                        NOGC(a);
                                        for (int i = 0; ; ++i) {
                                                push(INTEGER(i));
                                                call(vp, &subscript, 1, 0, true);
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
                                        if (subscript.integer < 0) {
                                                subscript.integer += container.array->count;
                                        }
                                        if (subscript.integer < 0 || subscript.integer >= container.array->count) {
                        OutOfRange:
                                                vm_panic("array index out of range in subscript expression");
                                        }
                                        push(container.array->items[subscript.integer]);
                                } else {
                                        vm_panic("non-integer array index used in subscript expression");
                                }
                                break;
                        case VALUE_TUPLE:
                                if (subscript.type == VALUE_INTEGER) {
                                        if (subscript.integer < 0)
                                                subscript.integer += container.count;
                                        if (subscript.integer < 0 || subscript.integer >= container.count)
                                                vm_panic("list index out of range in subscript expression");
                                        push(container.items[subscript.integer]);
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
                        case VALUE_OBJECT:
                                vp = class_method(container.class, "__subscript__");
                                if (vp != NULL) {
                                        push(subscript);
                                        call(vp, &container, 1, 0, false);
                                } else {
                                        goto BadContainer;
                                }
                                break;
                        case VALUE_CLASS:
                                push(subscript);
                                push(container);
                                n = 1;
                                b = false;
                                method = "__subscript__";
                                h = strhash(method);
                                goto CallMethod;
                        case VALUE_NIL:
                                push(NIL);
                                break;
                        default:
BadContainer:
                                vm_panic("invalid container in subscript expression: %s", value_show(&container));
                        }
                        break;
                CASE(NOT)
                        v = pop();
                        push(unary_operator_not(&v));
                        break;
                CASE(QUESTION)
                        if (top()->type == VALUE_NIL) {
                                *top() = BOOLEAN(false);
                        } else {
                                n = 0;
                                b = false;
                                method = "__question__";
                                h = strhash(method);
                                goto CallMethod;
                        }
                        break;
                CASE(NEG)
                        v = pop();
                        push(unary_operator_negate(&v));
                        break;
                CASE(COUNT)
                        v = pop();
                        switch (v.type) {
                        case VALUE_BLOB:   push(INTEGER(v.blob->count));  break;
                        case VALUE_ARRAY:  push(INTEGER(v.array->count)); break;
                        case VALUE_DICT:   push(INTEGER(v.dict->count));  break;
                        case VALUE_STRING:
                                push(get_string_method("len")(&v, 0));
                                break;
                        case VALUE_OBJECT:
                                push(v);
                                n = 0;
                                b = false;
                                method = "__len__";
                                h = strhash(method);
                                goto CallMethod;
                        default: vm_panic("# applied to operand of invalid type: %s", value_show(&v));
                        }
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
                CASE(CHECK_MATCH)
                        if (top()->type == VALUE_CLASS) {
                                v = pop();
                                switch (top()->type) {
                                case VALUE_INTEGER:  *top() = BOOLEAN(class_is_subclass(CLASS_INT, v.class));      break;
                                case VALUE_REAL:     *top() = BOOLEAN(class_is_subclass(CLASS_FLOAT, v.class));    break;
                                case VALUE_BOOLEAN:  *top() = BOOLEAN(class_is_subclass(CLASS_BOOL, v.class));     break;
                                case VALUE_ARRAY:    *top() = BOOLEAN(class_is_subclass(CLASS_ARRAY, v.class));    break;
                                case VALUE_STRING:   *top() = BOOLEAN(class_is_subclass(CLASS_STRING, v.class));   break;
                                case VALUE_BLOB:     *top() = BOOLEAN(class_is_subclass(CLASS_BLOB, v.class));     break;
                                case VALUE_DICT:     *top() = BOOLEAN(class_is_subclass(CLASS_DICT, v.class));     break;
                                case VALUE_METHOD:
                                case VALUE_BUILTIN_METHOD:
                                case VALUE_BUILTIN_FUNCTION:
                                case VALUE_FUNCTION: *top() = BOOLEAN(class_is_subclass(CLASS_FUNCTION, v.class)); break;
                                case VALUE_REGEX:    *top() = BOOLEAN(class_is_subclass(CLASS_REGEX, v.class));    break;
                                case VALUE_OBJECT:
                                        *top() = BOOLEAN(top()->type == VALUE_OBJECT &&
                                                         class_is_subclass(top()->class, v.class));                break;
                                default:             *top() = BOOLEAN(false);                                      break;
                                }
                        } else if (top()->type == VALUE_BOOLEAN) {
                                v = pop();
                                *top() = v;
                        } else {
                                n = 1;
                                b = false;
                                method = "__match__";
                                h = strhash(method);
                                goto CallMethod;
                        }
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

                        while (*ip != ((char)0xFF))
                                ++ip;
                        ++ip;

                        v.info = (int *) ip;

                        int hs = v.info[0];
                        int size  = v.info[1];
                        int ncaps = v.info[2];
                        int bound = v.info[3];

                        LOG("Header size: %d", hs);
                        LOG("Code size: %d", size);
                        LOG("Bound: %d", bound);
                        LOG("ncaps: %d", ncaps);
                        LOG("Name: %s", value_show(&v));

                        ip += size + hs;

                        if (ncaps > 0) {
                                LOG("Allocating ENV for %d caps", ncaps);
                                v.env = gc_alloc_object(ncaps * sizeof (struct value *), GC_ENV);
                                GC_ENABLED = false;

                                for (int i = 0; i < ncaps; ++i) {
                                        READVALUE(b);
                                        struct value *p = poptarget();
                                        if (b) {
                                                if (p->type == VALUE_REF) {
                                                        /* This variable was already captured, just refer to the same object */
                                                        v.env[i] = p->ptr;
                                                } else {
                                                        // TODO: figure out if this is getting freed too early
                                                        struct value *new = gc_alloc_object(sizeof (struct value), GC_VALUE);
                                                        *new = *p;
                                                        *p = REF(new);
                                                        v.env[i] = new;
                                                }
                                        } else {
                                                v.env[i] = p;
                                        }
                                }

                                GC_ENABLED = true;
                        } else {
                                LOG("Setting ENV to NULL");
                                v.env = NULL;
                        }

                        push(v);
                        break;
                }
                CASE(TAIL_CALL)
                        tco = true;
                        break;
                CASE(CALL)
                        v = pop();
                        READVALUE(n);
                        if (n == -1) {
                                n = stack.count - *vec_pop(sp_stack);
                        }

                        READVALUE(nkw);

                        if (tco) {
                                vec_pop(frames);
                                ip = *vec_pop(calls);
                                tco = false;
                        }

                        /*
                         * Move all the keyword args into a dict.
                         */
                        if (nkw > 0) {
                CallKwArgs:
                                container = DICT(dict_new());
                                NOGC(container.dict);
                                for (int i = 0; i < nkw; ++i) {
                                        dict_put_member(container.dict, ip, pop());
                                        ip += strlen(ip) + 1;
                                }
                                push(container);
                                OKGC(container.dict);
                        }

                Call:
                        gc_push(&v);
                        switch (v.type) {
                        case VALUE_FUNCTION:
                                LOG("CALLING %s with %d arguments", value_show(&v), n);
                                print_stack(n);
                                call(&v, NULL, n, nkw, false);
                                break;
                        case VALUE_BUILTIN_FUNCTION:
                                if (nkw > 0) {
                                        pop();
                                        nkw = 0;
                                }
                                v = v.builtin_function(n);
                                stack.count -= n;
                                push(v);
                                break;
                        case VALUE_GENERATOR:
                                call_co(&v, n);
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
                                vp = class_method(v.class, "init");
                                if (v.class < CLASS_PRIMITIVE && v.class != CLASS_OBJECT) {
                                        if (vp != NULL) {
                                                call(vp, NULL, n, nkw, true);
                                        } else {
                                                vm_panic("primitive class has no init method. was prelude loaded?");
                                        }
                                } else {
                                        value = OBJECT(object_new(), v.class);
                                        if (vp != NULL) {
                                                call(vp, &value, n, nkw, true);
                                                pop();
                                        } else {
                                                stack.count -= n;
                                        }
                                        push(value);
                                }
                                break;
                        case VALUE_METHOD:
                                call(v.method, v.this, n, nkw, false);
                                break;
                        case VALUE_REGEX:
                                if (n != 1)
                                        vm_panic("attempt to apply a regex to an invalid number of values");
                                value = peek();
                                if (value.type != VALUE_STRING)
                                        vm_panic("attempt to apply a regex to a non-string: %s", value_show(&value));
                                push(v);
                                v = get_string_method("match!")(&value, 1);
                                pop();
                                *top() = v;
                                break;
                        case VALUE_BUILTIN_METHOD:
                                if (nkw > 0) {
                                        pop();
                                        nkw = 0;
                                }
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
                        nkw = 0;
                        break;
                CASE(TRY_CALL_METHOD)
                CASE(CALL_METHOD)
                        b = ip[-1] == INSTR_TRY_CALL_METHOD;

                        READVALUE(n);
                        if (n == -1) {
                                n = stack.count - *vec_pop(sp_stack) - 1;
                        }

                        method = ip;
                        ip += strlen(ip) + 1;

                        READVALUE(h);

                        READVALUE(nkw);

                CallMethod:
                        LOG("METHOD = %s, n = %d", method, n);
                        print_stack(5);

                        value = peek();
                        vp = NULL;
                        func = NULL;
                        struct value *self = NULL;

                        if (tco) {
                                vec_pop(frames);
                                ip = *vec_pop(calls);
                                tco = false;
                        }

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
                        if (self == NULL && (self = &value)) switch (value.type & ~VALUE_TAGGED) {
                        case VALUE_TAG:
                                vp = tags_lookup_method(value.tag, method, h);
                                self = NULL;
                                break;
                        case VALUE_STRING:
                                func = get_string_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(CLASS_STRING, method, h);
                                break;
                        case VALUE_DICT:
                                func = get_dict_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(CLASS_DICT, method, h);
                                break;
                        case VALUE_ARRAY:
                                func = get_array_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(CLASS_ARRAY, method, h);
                                break;
                        case VALUE_BLOB:
                                func = get_blob_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(CLASS_BLOB, method, h);
                                break;
                        case VALUE_INTEGER:
                                vp = class_lookup_method(CLASS_INT, method, h);
                                break;
                        case VALUE_REAL:
                                vp = class_lookup_method(CLASS_FLOAT, method, h);
                                break;
                        case VALUE_BOOLEAN:
                                vp = class_lookup_method(CLASS_BOOL, method, h);
                                break;
                        case VALUE_REGEX:
                                vp = class_lookup_method(CLASS_REGEX, method, h);
                                break;
                        case VALUE_FUNCTION:
                        case VALUE_BUILTIN_FUNCTION:
                        case VALUE_METHOD:
                        case VALUE_BUILTIN_METHOD:
                                vp = class_lookup_method(CLASS_FUNCTION, method, h);
                                break;
                        case VALUE_GENERATOR:
                                vp = class_lookup_method(CLASS_GENERATOR, method, h);
                                break;
                        case VALUE_CLASS: /* lol */
                                vp = class_lookup_immediate(CLASS_CLASS, method, h);
                                if (vp == NULL) {
                                        vp = class_lookup_method(value.class, method, h);
                                }
                                break;
                        case VALUE_OBJECT:
                                vp = table_lookup(value.object, method, h);
                                if (vp == NULL) {
                                        vp = class_lookup_method(value.class, method, h);
                                } else {
                                        self = NULL;
                                }
                                break;
                        case VALUE_NIL:
                                stack.count -= (n + 1);
                                push(NIL);
                                continue;
                        }

                        if (func != NULL) {
                                value.type &= ~VALUE_TAGGED;
                                value.tags = 0;
                                pop();
                                gc_push(&value);
                                v = func(&value, n);
                                stack.count -= n;
                                push(v);
                                gc_pop();
                        } else if (vp != NULL) {
                                pop();
                                if (self != NULL) {
                                        v = METHOD(method, vp, self);
                                } else {
                                        v = *vp;
                                }
                                if (nkw > 0) {
                                        goto CallKwArgs;
                                } else {
                                        goto Call;
                                }
                        } else if (b) {
                                stack.count -= (n + 1);
                                push(NIL);
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
                CASE(RETURN)
                Return:
                        n = vec_last(frames)->fp;
                        if (ip[-1] == INSTR_MULTI_RETURN) {
                                READVALUE(rc);
                                stack.count -= rc;
                                for (int i = 0; i <= rc; ++i) {
                                        stack.items[n + i] = top()[i];
                                }
                        } else {
                                stack.items[n] = peek();
                        }
                        stack.count = n + 1;
                        LOG("POPPING FRAME");
                        vec_pop(frames);
                CASE(RETURN_PRESERVE_CTX)
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
        return Error;
}

bool
vm_init(int ac, char **av)
{
        vec_init(stack);
        vec_init(calls);
        vec_init(targets);

        pcre_malloc = malloc;
        JITStack = pcre_jit_stack_alloc(JIT_STACK_START, JIT_STACK_MAX);
        if (JITStack == NULL) {
                panic("out of memory");
        }

        curl_global_init(CURL_GLOBAL_ALL);

        srand48(time(NULL));
        srandom(lrand48());

        compiler_init();

        add_builtins(ac, av);

        char *prelude = compiler_load_prelude();
        if (prelude == NULL) {
                Error = compiler_error();
                return false;
        }

        if (setjmp(jb) != 0) {
                Error = ERR;
                return false;
        }

        vm_exec(prelude);

        sqlite_load();

        return true;
}

noreturn void
vm_panic(char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        struct location start;
        struct location end;

        int sz = ERR_SIZE - 1;

        int n = snprintf(ERR, sz, "%s%sRuntimeError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        n += vsnprintf(ERR + n, max(sz - n, 0), fmt, ap);
        va_end(ap);

        if (n < sz)
                ERR[n++] = '\n';

        for (int i = 0; n < sz; ++i) {
                char const *file = compiler_get_location(ip, &start, &end);
                char buffer[512];

                snprintf(
                        buffer,
                        sizeof buffer - 1,
                        "%36s %s%s%s:%s%d%s:%s%d%s",
                        (i == 0) ? "at" : "from",
                        TERM(34),
                        file,
                        TERM(39),
                        TERM(33),
                        start.line + 1,
                        TERM(39),
                        TERM(33),
                        start.col + 1,
                        TERM(39)
                );

                char const *where = buffer;
                int m = strlen(buffer) - 6*strlen(TERM(00));

                while (m > 36) {
                        m -= 1;
                        where += 1;
                }

                n += snprintf(
                        ERR + n,
                        sz - n,
                        "\n%s near: ",
                        where
                );

                if (start.s == NULL) {
                        start.s = "\n(unknown location)" + 1;
                        end.s = start.s;
                }

                char const *prefix = start.s;
                while (prefix[-1] != '\0' && prefix[-1] != '\n')
                        --prefix;

                while (isspace(prefix[0]))
                        ++prefix;

                int before = start.s - prefix;
                int length = end.s - start.s;
                int after = strcspn(end.s, "\n");

                n += snprintf(
                        ERR + n,
                        sz - n,
                        "%s%.*s%s%s%.*s%s%s%.*s%s",
                        TERM(32),
                        before,
                        prefix,
                        (i == 0) ? TERM(1) : "",
                        (i == 0) ? TERM(91) : TERM(31),
                        length,
                        start.s,
                        TERM(32),
                        TERM(22),
                        after,
                        end.s,
                        TERM(39)
                );

                n += snprintf(
                        ERR + n,
                        sz - n,
                        "\n\t%*s%s%s",
                        before + 35,
                        "",
                        (i == 0) ? TERM(1) : "",
                        (i == 0) ? TERM(91) : TERM(31)
                );

                for (int i = 0; i < length && n < sz; ++i)
                        ERR[n++] = '^';

                n += snprintf(
                        ERR + n,
                        sz - n,
                        "%s%s",
                        TERM(39),
                        TERM(22)
                );
Next:
                if (frames.count == 0) {
                        break;
                }

                ip = vec_pop(frames)->ip;
        }

        LOG("VM Error: %s", ERR);

        longjmp(jb, 1);
}

bool
vm_execute_file(char const *path)
{
        char *source = slurp(path);
        if (source == NULL) {
                Error = "failed to read source file";
                return false;
        }

        filename = path;

        bool success = vm_execute(source);
        /*
         * When we read the file, we copy into an allocated buffer with a 0 byte at
         * the beginning, so we need to subtract 1 here to get something appropriate
         * for free().
         */
        gc_free(source - 1);

        filename = NULL;

        return success;
}

bool
vm_execute(char const *source)
{
        if (filename == NULL)
                filename = "(repl)";

        char *code = compiler_compile_source(source, filename);
        if (code == NULL) {
                Error = compiler_error();
                LOG("compiler error was: %s", Error);
                return false;
        }

        if (setjmp(jb) != 0) {
                gc_clear_root_set();
                stack.count = 0;
                sp_stack.count = 0;
                try_stack.count = 0;
                targets.count = 0;
                Error = ERR;
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
                call(f, NULL, argc, 0, true);
                return pop();
        case VALUE_METHOD:
                call(f->method, f->this, argc, 0, true);
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
                init = class_method(f->class, "init");
                if (f->class < CLASS_PRIMITIVE) {
                        if (init != NULL) {
                                call(init, NULL, argc, 0, true);
                                return pop();
                        } else {
                                vm_panic("Couldn't find init method for built-in class. Was prelude loaded?");
                        }
                } else {
                        r = OBJECT(object_new(), f->class);
                        if (init != NULL) {
                                call(init, &r, argc, 0, true);
                                pop();
                        } else {
                                stack.count -= (argc + 1);
                        }
                        return r;
                }
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
                call(f, NULL, argc, 0, true);
                return pop();
        case VALUE_METHOD:
                call(f->method, f->this, argc, 0, true);
                return pop();
        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(argc);
                stack.count -= argc;
                return r;
        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(f->this, argc);
                stack.count -= argc;
                return r;
        default:
                abort();
        }
}

void
vm_mark(void)
{
        for (int i = 0; i < Globals.count; ++i)
                value_mark(&Globals.items[i]);

        for (int i = 0; i < stack.count; ++i)
                value_mark(&stack.items[i]);

        for (int i = 0; i < targets.count; ++i)
                value_mark(targets.items[i].t);

        for (int i = 0; i < sigfns.count; ++i)
                value_mark(&sigfns.items[i].f);

        for (int i = 0; i < frames.count; ++i) {
                value_mark(&frames.items[i].f);
        }
}
