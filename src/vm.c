#include <time.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <setjmp.h>
#include <stdarg.h>
#include <errno.h>
#include <stdnoreturn.h>

#include <pcre.h>

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
#include "functions.h"
#include "array.h"
#include "str.h"
#include "blob.h"
#include "tags.h"
#include "object.h"
#include "class.h"
#include "utf8.h"

#define READVALUE(s) (memcpy(&s, ip, sizeof s), (ip += sizeof s))
#define CASE(i)      case INSTR_ ## i: LOG("executing instr: " #i);

static char halt = INSTR_HALT;

static jmp_buf jb;

static struct variable **vars;
static vec(struct value) stack;
static vec(char *) callstack;
static vec(size_t) sp_stack;
static vec(struct value *) targetstack;
static char *ip;

static int symbol_count = 0;

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
        v->prev = NULL;
        v->next = next;
        return v;
}

/*
 * This relies on no other symbols being introduced to the compiler
 * up until the point that this is called. i.e., it assumes that the
 * first built-in function should have symbol 0. I think this is ok.
 */
static void
add_builtins(int ac, char **av)
{
        resize(vars, sizeof *vars * builtin_count + 1);

        for (int i = 0; i < builtin_count; ++i) {
                compiler_introduce_symbol(builtins[i].module, builtins[i].name);
                vars[i] = newvar(NULL);
                vars[i]->value = builtins[i].value;
        }

        struct array *args = value_array_new();
        NOGC(args);

        for (int i = 1; i < ac; ++i)
                value_array_push(args, STRING_NOGC(av[i], strlen(av[i])));

        compiler_introduce_symbol("os", "args");
        vars[builtin_count] = newvar(NULL);
        vars[builtin_count]->value = ARRAY(args);

        symbol_count = builtin_count + 1;
}

inline static struct value *
top(void)
{
        return &stack.items[stack.count - 1];
}

inline static struct value
pop(void)
{
        LOG("popping %s", value_show(top()));
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
        LOG("pushing %s", value_show(&v));
        vec_push(stack, v);
}

inline static struct value *
poptarget(void)
{
        return *vec_pop(targetstack);
}

inline static struct value *
peektarget(void)
{
        return targetstack.items[targetstack.count - 1];
}

inline static void
pushtarget(struct value *v)
{
        vec_push(targetstack, v);
}

inline static void
call(struct value *f, struct value *self, int n, bool exec)
{
        for (int i = 0; i < f->bound; ++i)
                vars[f->symbols[i]] = newvar(vars[f->symbols[i]]);

        bool has_self = (f->params > 0) && (self != NULL);

        int params = f->params - has_self;

        /* throw away ignored arguments */
        while (n > params)
                pop(), --n;

        /* default missing parameters to nil */
        for (int i = n; i < params; ++i)
                vars[f->symbols[i + has_self]]->value = NIL;

        /* fill in the rest of the arguments */
        while (n --> 0)
                vars[f->symbols[n + has_self]]->value = pop();

        /* fill in 'self' / 'this' */
        if (has_self)
                vars[f->symbols[0]]->value = *self;

        for (int i = 0; i < f->refs->count; ++i) {
                struct reference ref = f->refs->refs[i];
                LOG("resolving reference to %p", (void *) ref.pointer);
                memcpy(f->code + ref.offset, &ref.pointer, sizeof ref.pointer);
        }

        if (exec) {
                vec_push(callstack, &halt);
                vm_exec(f->code);
        } else {
                vec_push(callstack, ip);
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
        int n, index, tag, l, r;

        struct value left, right, v, key, value, container, subscript, *vp;
        char *str;

        value_vector args;
        vec_init(args);

        struct value (*func)(struct value *, value_vector *);

        struct variable *next;

        for (;;) {
                switch (*ip++) {
                CASE(PUSH_VAR)
                        READVALUE(s);
                        LOG("new var for %d", (int) s);
                        vars[s] = newvar(vars[s]);
                        break;
                CASE(POP_VAR)
                        READVALUE(s);
                        next = vars[s]->next;
                        if (vars[s]->captured) {
                                gc_register(vars[s]);
                                LOG("detaching captured variable");
                                vars[s]->next->prev = NULL;
                        }
                        vars[s] = next;
                        break;
                CASE(LOAD_VAR)
                        READVALUE(s);
                        LOG("loading %d", (int) s);
                        push(vars[s]->value);
                        break;
                CASE(CHECK_VARS)
                        READVALUE(n);
                        while (n --> 0) {
                                READVALUE(s);
                                if (vars[s]->captured) {
                                        struct variable *next = newvar(vars[s]->next);
                                        if (vars[s]->next != NULL)
                                                vars[s]->next->prev = vars[s]->prev;
                                        gc_register(vars[s]);
                                        next->value = vars[s]->value;
                                        vars[s] = next;
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
                        LOG("JUMPING %d", n);
                        ip += n;
                        break;
                CASE(JUMP_IF)
                        READVALUE(n);
                        v = pop();
                        if (value_truthy(&v)) {
                                LOG("JUMPING %d", n);
                                ip += n;
                        }
                        break;
                CASE(JUMP_IF_NOT)
                        READVALUE(n);
                        v = pop();
                        if (!value_truthy(&v)) {
                                LOG("JUMPING %d", n);
                                ip += n;
                        }
                        break;
                CASE(TARGET_VAR)
                        READVALUE(s);
                        LOG("targetting %d", (int) s);
                        pushtarget(&vars[s]->value);
                        break;
                CASE(TARGET_REF)
                        READVALUE(s);
                        LOG("ref = %p", (void *) s);
                        pushtarget(&((struct variable *) s)->value);
                        break;
                CASE(TARGET_MEMBER)
                        v = pop();
                        if (!(v.type & VALUE_OBJECT))
                                vm_panic("assignment to member of non-object");
                        vp = table_lookup(v.object, ip);
                        if (vp != NULL)
                                pushtarget(vp);
                        else
                                pushtarget(table_add(v.object, ip, NIL));
                        ip += strlen(ip) + 1;
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
                                pushtarget(&container.array->items[subscript.integer]);
                        } else if (container.type == VALUE_DICT) {
                                pushtarget(dict_put_key_if_not_exists(container.dict, subscript));
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
                        READVALUE(index);
                        READVALUE(n);
                        if (top()->type != VALUE_ARRAY) {
                                LOG("cannot do rest: top is not an array");
                                ip += n;
                        } else {
                                LOG("Assigning rest to: %d", (int) s);
                                vars[s]->value = ARRAY(value_array_new());
                                vec_push_n(*vars[s]->value.array, top()->array->items + index, top()->array->count - index);
                        }
                        break;
                CASE(DIE_IF_NIL)
                        if (top()->type == VALUE_NIL)
                                vm_panic("failed to match %s against the non-nil pattern", value_show(top()));
                        break;
                CASE(UNTAG_OR_DIE)
                        READVALUE(tag);
                        if (!tags_same(tags_first(top()->tags), tag)) {
                                vm_panic("failed to match %s against the tag %s", value_show(top()), tags_name(tag));
                        } else {
                                top()->tags = tags_pop(top()->tags);
                                top()->type &= ~VALUE_TAGGED;
                        }
                        break;
                CASE(BAD_MATCH)
                        vm_panic("expression did not match any patterns in match expression");
                        break;
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
                        READVALUE(index);
                        READVALUE(n);
                        LOG("trying to index: %s", value_show(top()));
                        if (top()->type != VALUE_ARRAY || top()->array->count <= index)
                                ip += n;
                        else
                                push(top()->array->items[index]);
                        break;
                CASE(TRY_TAG_POP)
                        READVALUE(tag);
                        READVALUE(n);
                        if (!tags_same(top()->tags, tag)) {
                                LOG("failed tag pop");
                                ip += n;
                        } else {
                                LOG("tag pop successful");
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
                        LOG("reference is: %p", (void *) s);
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
                        for (int i = 0; i < n; ++i)
                                vec_push(*v.array, pop());

                        push(v);
                        break;
                CASE(DICT)
                        v = DICT(dict_new());

                        READVALUE(n);
                        for (int i = 0; i < n; ++i) {
                                value = pop();
                                key = pop();
                                dict_put_value(v.dict, key, value);
                        }

                        push(v);
                        break;
                CASE(NIL)
                        push(NIL);
                        break;
                CASE(TO_STRING)
                        v = pop();
                        v = builtin_str(&(value_vector){ .items = &v, .count = 1 });
                        push(v);
                        break;
                CASE(FOR_EACH)
                        v = pop();
                        READVALUE(n);
                        char *first = ip;
                        char instr = *ip;

                        switch (v.type) {
                        case VALUE_ARRAY:
                                gc_push(&v);
                                for (int i = 0; *first != INSTR_HALT && i < v.array->count; ++i) {
                                        push(v.array->items[i]);
                                        vm_exec(ip);
                                }
                                gc_pop();
                                break;
                        case VALUE_DICT:
                                for (int i = 0; i < DICT_NUM_BUCKETS; ++i) {
                                        struct dict_node *node = v.dict->buckets[i];
                                        while (node != NULL) {
                                                push(node->key);
                                                vm_exec(ip);
                                                node = node->next;
                                        }
                                }
                                break;
                        case VALUE_BLOB:
                                for (int i = 0; i < v.blob->count; ++i) {
                                        push(INTEGER(v.blob->items[i]));
                                        vm_exec(ip);
                                }
                                break;
                        case VALUE_STRING:
                        {
                                int offset = 0;
                                while (offset < v.bytes) {
                                        int bytes = utf8_char_len(v.string + offset);
                                        push(STRING_VIEW(v, offset, bytes));
                                        vm_exec(ip);
                                        offset += bytes;
                                }
                                break;
                        }
                        case VALUE_OBJECT:
                        {
                                vp = class_lookup_method(v.class, "__iter__");
                                if (vp == NULL)
                                        goto non_iter;

                                call(vp, &v, 0, true);
                                struct value iterator = pop();

                                if (iterator.type != VALUE_OBJECT || (vp = class_lookup_method(iterator.class, "__next__")) == NULL)
                                        vm_panic("__iter__ returned a non-iterator");

                                gc_push(&v);

                                call(vp, &iterator, 0, true);
                                struct value item = pop();

                                gc_push(&iterator);

                                while (item.type != VALUE_NIL) {
                                        push(item);
                                        vm_exec(ip);
                                        call(vp, &iterator, 0, true);
                                        item = pop();
                                }

                                gc_pop();
                                gc_pop();

                                break;
                        }
                        default:
                        non_iter:
                                vm_panic("for-each on non-iterable value");
                        }

                        *first = instr;
                        ip += + n;

                        break;
                CASE(BREAK_EACH)
                        *save = INSTR_HALT;
                        goto halt;
                CASE(CONCAT_STRINGS)
                        READVALUE(n);
                        LOG("n = %d", n);
                        k = 0;
                        for (index = stack.count - n; index < stack.count; ++index)
                                k += stack.items[index].bytes;
                        str = value_string_alloc(k);
                        v = STRING(str, k, str);
                        k = 0;
                        for (index = stack.count - n; index < stack.count; ++index) {
                                memcpy(str + k, stack.items[index].string, stack.items[index].bytes);
                                k += stack.items[index].bytes;
                        }
                        stack.count -= n - 1;
                        stack.items[stack.count - 1] = v;
                        break;
                CASE(RANGE)
                        READVALUE(l);
                        READVALUE(r);
                        right = pop();
                        left = pop();
                        if (right.type != VALUE_INTEGER || left.type != VALUE_INTEGER)
                                vm_panic("non-integer used as bound in range");
                        v = ARRAY(value_array_new());
                        push(v);
                        value_array_reserve(v.array, abs(right.integer - left.integer) + 2);
                        if (left.integer < right.integer)
                                for (int i = left.integer + l; i <= right.integer + r; ++i)
                                        v.array->items[v.array->count++] = INTEGER(i);
                        else
                                for (int i = left.integer - l; i >= right.integer - r; --i)
                                        v.array->items[v.array->count++] = INTEGER(i);
                        break;
                CASE(MEMBER_ACCESS)
                        v = pop();

                        char const *member = ip;
                        ip += strlen(ip) + 1;

                        vp = NULL;
                        if (v.type & VALUE_TAGGED) for (int tags = v.tags; tags != 0; tags = tags_pop(tags)) {
                                vp = tags_lookup_method(tags_first(tags), member);
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
                                vp = table_lookup(v.object, member);
                                if (vp != NULL) {
                                        push(*vp);
                                        break;
                                }
                                vp = class_lookup_method(v.class, member);
                                if (vp != NULL) {
                                        this = gc_alloc_object(sizeof *this, GC_VALUE);
                                        *this = v;
                                        push(METHOD(member, vp, this));
                                        break;
                                }
                                vm_panic("attempt to access non-existent member '%s' of %s", member, value_show(&v));
                                break;
                        case VALUE_TAG:
                                vp = tags_lookup_method(v.tag, member);
                                push(vp == NULL ? NIL : *vp);
                                break;
                        case VALUE_CLASS:
                                vp = class_lookup_method(v.class, member);
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
                                if (subscript.type != VALUE_INTEGER)
                                        vm_panic("non-integer array index used in subscript expression");
                                if (subscript.integer < 0)
                                        subscript.integer += container.array->count;
                                if (subscript.integer < 0 || subscript.integer >= container.array->count)
                                        vm_panic("array index out of range in subscript expression");
                                push(container.array->items[subscript.integer]);
                                break;
                        case VALUE_STRING:
                                push(get_string_method("char")(&container, (&(value_vector){ .count = 1, .items = &subscript })));
                                break;
                        case VALUE_BLOB:
                                push(get_blob_method("get")(&container, (&(value_vector){ .count = 1, .items = &subscript })));
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
                CASE(INC) // only used for internal (hidden) variables
                        READVALUE(s);
                        ++vars[s]->value.integer;
                        break;
                CASE(PRE_INC)
                        if (peektarget()->type != VALUE_INTEGER)
                                vm_panic("pre-increment applied to non-integer");
                        ++peektarget()->integer;
                        push(*poptarget());
                        break;
                CASE(POST_INC)
                        if (peektarget()->type != VALUE_INTEGER)
                                vm_panic("post-increment applied to non-integer");
                        push(*peektarget());
                        ++poptarget()->integer;
                        break;
                CASE(PRE_DEC)
                        if (peektarget()->type != VALUE_INTEGER)
                                vm_panic("pre-decrement applied to non-integer");
                        --peektarget()->integer;
                        push(*poptarget());
                        break;
                CASE(POST_DEC)
                        if (peektarget()->type != VALUE_INTEGER)
                                vm_panic("post-decrement applied to non-integer");
                        push(*peektarget());
                        --poptarget()->integer;
                        break;
                CASE(MUT_ADD)
                        vp = poptarget();
                        if (vp->type == VALUE_ARRAY) {
                                if (top()->type != VALUE_ARRAY)
                                        vm_panic("attempt to add non-array to array");
                                value_array_extend(vp->array, pop().array);
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
                        v = pop();
                        *vp = binary_operator_subtraction(vp, &v);
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
                                NOGC(v.refs);
                                class_add_method(class, ip, v);
                                ip += strlen(ip) + 1;
                        }
                        if (super != -1)
                                class_copy_methods(class, super);
                        break;
                }
                CASE(FUNCTION)
                {
                        v.tags = 0;
                        v.type = VALUE_FUNCTION;
                        v.this = NULL;

                        int params;
                        int bound;

                        READVALUE(params);
                        READVALUE(bound);

                        v.bound = bound;
                        v.params = params;

                        while (*ip != ((char)0xFF))
                                ++ip;
                        ++ip;

                        v.symbols = (int *) ip;
                        ip += bound * sizeof (int);

                        READVALUE(n);
                        v.code = ip;
                        ip += n;

                        READVALUE(n);
                        v.refs = ref_vector_new(n);
                        LOG("function contains %d reference(s)", n);
                        for (int i = 0; i < n; ++i) {
                                READVALUE(s);
                                READVALUE(off);
                                vars[s]->captured = true;
                                struct reference ref = { .pointer = (uintptr_t) vars[s], .offset = off };
                                LOG("it refers to symbol %d", (int) s);
                                LOG("it refers to pointer %p", (void *) ref.pointer);
                                v.refs->refs[i] = ref;
                        }

                        push(v);
                        break;
                }
                CASE(CALL)
                        v = pop();
                        READVALUE(n);

                        switch (v.type) {
                        case VALUE_FUNCTION:
                                call(&v, NULL, n, false);
                                break;
                        case VALUE_BUILTIN_FUNCTION:
                                vec_reserve(args, n);
                                args.count = n;
                                while (n --> 0)
                                        args.items[n] = pop();
                                push(v.builtin_function(&args));
                                args.count = 0;
                                break;
                        case VALUE_TAG:
                                if (n != 1)
                                        vm_panic("attempt to apply a tag to an invalid number of values");
                                top()->tags = tags_push(top()->tags, v.tag);
                                top()->type |= VALUE_TAGGED;
                                break;
                        case VALUE_CLASS:
                                value = OBJECT(object_new(), v.class);
                                vp = class_lookup_method(v.class, "init");
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
                        case VALUE_BUILTIN_METHOD:
                                vec_reserve(args, n);
                                args.count = n;
                                index = 0;

                                for (struct value const *a = stack.items + stack.count - n - 1; index < n; ++index, ++a)
                                        args.items[index] = *a;

                                value = v.builtin_method(v.this, &args);

                                stack.count -= n;
                                stack.items[stack.count - 1] = value;

                                break;
                        case VALUE_NIL:
                                stack.count -= n;
                                push(NIL);
                                break;
                        default:
                                vm_panic("attempt to call non-callable value %s", value_show(&v));
                        }

                        break;
                CASE(CALL_METHOD)
                        
                        value = peek();

                        vp = NULL;
                        func = NULL;
                        struct value *self = NULL;

                        char const *method = ip;
                        ip += strlen(ip) + 1;

                        for (int tags = value.tags; tags != 0; tags = tags_pop(tags)) {
                                vp = tags_lookup_method(tags_first(tags), method);
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
                                vp = tags_lookup_method(value.tag, method);
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
                        case VALUE_OBJECT:
                                self = &value;
                        case VALUE_CLASS:
                                vp = class_lookup_method(value.class, method);
                                break;
                        case VALUE_NIL:
                                pop();
                                READVALUE(n);
                                stack.count -= n;
                                push(NIL);
                                continue;
                        }

                        if (func != NULL) {
                                READVALUE(n);
                                vec_reserve(args, n);
                                args.count = n;
                                index = 0;

                                for (struct value const *a = stack.items + stack.count - n - 1; index < n; ++index, ++a)
                                        args.items[index] = *a;

                                value.type &= ~VALUE_TAGGED;
                                value.tags = 0;

                                v = func(&value, &args);

                                stack.count -= n;
                                stack.items[stack.count - 1] = v;
                        } else if (vp != NULL) {
                                --stack.count;
                                READVALUE(n);
                                call(vp, self, n, false);
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
                CASE(RETURN)
                        ip = *vec_pop(callstack);
                        break;
                CASE(HALT)
                halt:
                        free(args.items);
                        ip = save;
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
        vec_init(callstack);
        vec_init(targetstack);
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
        while (symbol_count < new_symbol_count) {
                LOG("SETTING %d TO NULL", symbol_count);
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
        while (symbol_count < new_symbol_count) {
                LOG("SETTING %d TO NULL", symbol_count);
                vars[symbol_count++] = NULL;
        }

        if (setjmp(jb) != 0) {
                gc_clear_root_set();
                vec_empty(stack);
                err_msg = err_buf;
                return false;
        }

        vm_exec(code);

        return true;
}

struct value
vm_eval_function(struct value *f, struct value *v)
{
        switch (f->type) {
        case VALUE_FUNCTION:
                if (v != NULL)
                        push(*v);
                call(f, NULL, v != NULL, true);
                return pop();
        case VALUE_METHOD:
                if (v != NULL)
                        push(*v);
                call(f->method, f->this, v != NULL, true);
                return pop();
        case VALUE_BUILTIN_FUNCTION:
                return f->builtin_function(&(value_vector){
                        .count = v != NULL,
                        .items = v
                });
        case VALUE_BUILTIN_METHOD:
                return f->builtin_method(f->this, &(value_vector){
                        .count = v != NULL,
                        .items = v
                });
        default:
                abort();
        }
}

struct value
vm_eval_function2(struct value *f, struct value *v1, struct value *v2)
{
        value_vector args;

        switch (f->type) {
        case VALUE_FUNCTION:
                push(*v1);
                push(*v2);
                call(f, NULL, 2, true);
                return pop();
        case VALUE_METHOD:
                push(*v1);
                push(*v2);
                call(f->method, f->this, 2, true);
                return pop();
        case VALUE_BUILTIN_FUNCTION:
                vec_init(args);
                vec_push(args, *v1);
                vec_push(args, *v2);
                return f->builtin_function(&args);
        default:
                abort();
        }
}

void
vm_mark(void)
{
        for (int i = 0; i < symbol_count; ++i)
                for (struct variable *v = vars[i]; v != NULL; v = v->next)
                        value_mark(&v->value);

        for (int i = 0; i < stack.count; ++i)
                value_mark(&stack.items[i]);
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

        if (!vm_execute(source)) {
                printf("error: %s\n", vm_error());
        }

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
