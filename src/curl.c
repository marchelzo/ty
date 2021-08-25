#include <curl/curl.h>

#include "value.h"
#include "alloc.h"
#include "vec.h"
#include "vm.h"
#include "table.h"
#include "object.h"
#include "util.h"

static vec(char) Buffer;

static size_t
write_function(char *ptr, size_t size, size_t nmemb, void *data)
{
        size_t n = size * nmemb;

        vec_push_n(Buffer, ptr, n);

        return n;
}

struct value
builtin_curl_init(int argc)
{
        if (argc != 0) {
                vm_panic("curl::init() expects no arguments but got %d", argc);
        }

        CURL *c = curl_easy_init();
        
        if (c == NULL) {
                vm_panic("curl_easy_init returned NULL");
        }

        if (curl_easy_setopt(c, CURLOPT_WRITEFUNCTION, write_function) != CURLE_OK) {
                vm_panic("failed to set CURLOPT_WRITEFUNCTION");
        }

        return PTR(c);
}

struct value
builtin_curl_mime(int argc)
{
        if (argc != 1) {
                vm_panic("curl::mime::init() expects 1 argument but got %d", argc);
        }

        struct value curl = ARG(0);
        if (curl.type != VALUE_PTR) {
                vm_panic("the first argument to curl::mime() must be a pointer");
        }

        curl_mime *m = curl_mime_init(curl.ptr);
        if (m == NULL) {
                vm_panic("curl_mime_init returned NULL");
        }

        return PTR(m);
}

struct value
builtin_curl_mime_add(int argc)
{
        if (argc != 1) {
                vm_panic("curl::mime::add() expects 1 argument but got %d", argc);
        }

        struct value mime = ARG(0);
        if (mime.type != VALUE_PTR) {
                vm_panic("the first argument to curl::mime::add() must be a pointer");
        }

        curl_mimepart *p = curl_mime_addpart(mime.ptr);
        if (p == NULL) {
                vm_panic("curl_mime_addpart returned NULL");
        }

        return PTR(p);
}

struct value
builtin_curl_mime_data(int argc)
{
        if (argc != 2) {
                vm_panic("curl::mime::data() expects 2 arguments but got %d", argc);
        }

        struct value part = ARG(0);
        if (part.type != VALUE_PTR) {
                vm_panic("the first argument to curl::mime::data() must be a pointer");
        }

        struct value data = ARG(1);
        switch (data.type) {
        case VALUE_STRING:
                curl_mime_data(part.ptr, data.string, data.bytes);
                break;
        case VALUE_BLOB:
                curl_mime_data(part.ptr, data.blob->items, data.blob->count);
                break;
        default:
                vm_panic("invalid data argument passed to curl::mime::data()");
        }

        return NIL;
}

struct value
builtin_curl_mime_name(int argc)
{
        if (argc != 2) {
                vm_panic("curl::mime::name() expects 2 arguments but got %d", argc);
        }

        struct value part = ARG(0);
        if (part.type != VALUE_PTR) {
                vm_panic("the first argument to curl::mime::name() must be a pointer");
        }

        Buffer.count = 0;

        struct value name = ARG(1);
        switch (name.type) {
        case VALUE_STRING:
                vec_push_n(Buffer, name.string, name.bytes);
                vec_push(Buffer, '\0');
                break;
        case VALUE_BLOB:
                vec_push_n(Buffer, name.blob->items, name.blob->count);
                vec_push(Buffer, '\0');
                break;
        default:
                vm_panic("invalid name argument passed to curl::mime::name()");
        }

        curl_mime_name(part.ptr, name.string);

        return NIL;
}

struct value
builtin_curl_slist_append(int argc)
{
        if (argc != 2) {
                vm_panic("curl::slist::append() expects 2 arguments but got %d", argc);
        }

        struct value slist = ARG(0);
        if (slist.type != VALUE_PTR) {
                vm_panic("the first argument to curl::slist::append() must be a pointer");
        }

        struct value s = ARG(1);
        if (s.type != VALUE_BLOB) {
                vm_panic("the second argument to curl::slist::append() must be a blob");
        }

        struct curl_slist *list = curl_slist_append(slist.ptr, s.blob->items);
        if (list == NULL) {
                vm_panic("out of memory");
        }

        return PTR(list);
}

struct value
builtin_curl_slist_free(int argc)
{
        if (argc != 1) {
                vm_panic("curl::slist::free() expects 1 argument but got %d", argc);
        }

        struct value slist = ARG(0);
        if (slist.type != VALUE_PTR) {
                vm_panic("the argument to curl::slist::free() must be a pointer");
        }

        curl_slist_free_all(slist.ptr);

        return NIL;
}

struct value
builtin_curl_setopt(int argc)
{
        if (argc < 2) {
                vm_panic("curl::setopt() expects at least 2 arguments but got %d", argc);
        }

        struct value curl = ARG(0);
        if (curl.type != VALUE_PTR) {
                vm_panic("the first argument to curl::setopt() must be a pointer");
        }

        struct value opt = ARG(1);
        if (opt.type != VALUE_INTEGER) {
                vm_panic("the second argument to curl::setopt() must be an integer");
        }

        struct value s;
        char buffer[1024];

        switch (opt.integer) {
        case CURLOPT_URL:
                s = ARG(2);
                if (s.type != VALUE_STRING) {
                        vm_panic("the value of CURLOPT_URL must be a string");
                }
                if (s.bytes >= sizeof buffer) {
                        vm_panic("CURLOPT_URL is too long");
                }
                memcpy(buffer, s.string, s.bytes);
                buffer[s.bytes] = '\0';
                return INTEGER(curl_easy_setopt(curl.ptr, CURLOPT_URL, buffer));
        case CURLOPT_POST:
                s = ARG(2);
                if (s.type != VALUE_INTEGER) {
                        vm_panic("the value of CURLOPT_POST must be an integer");
                }
                curl_easy_setopt(curl.ptr, CURLOPT_POST, (long)s.integer);
                break;
        case CURLOPT_POSTFIELDS:
                break;
        case CURLOPT_MIMEPOST:
                s = ARG(2);
                if (s.type != VALUE_PTR) {
                        vm_panic("the value of CURLOPT_MIMEPOST must be a pointer");
                }
                curl_easy_setopt(curl.ptr, CURLOPT_MIMEPOST, s.ptr);
                break;
        case CURLOPT_HTTPHEADER:
                s = ARG(2);
                if (s.type != VALUE_ARRAY) {
                        vm_panic("the value of CURLOPT_HTTPHEADER must be an pointer");
                }
                curl_easy_setopt(curl.ptr, CURLOPT_HTTPHEADER, s.ptr);
                break;
        default:
                vm_panic("invalid option passed to curl::setopt(): %d", opt.integer);
        }
}

struct value
builtin_curl_perform(int argc)
{
        if (argc != 1) {
                vm_panic("curl::perform() expects 1 argument but got %d", argc);
        }

        struct value curl = ARG(0);
        if (curl.type != VALUE_PTR) {
                vm_panic("the argument to curl::perform() must be a pointer");
        }
        
        vec_init(Buffer);

        CURLcode r = curl_easy_perform(curl.ptr);

        if (r != CURLE_OK) {
                vec_empty(Buffer);
                return INTEGER(r);
        }

        struct blob *b = value_blob_new();
        b->items = Buffer.items;
        b->count = Buffer.count;
        b->capacity = Buffer.capacity;

        vec_init(Buffer);

        return BLOB(b);
}

struct value
builtin_curl_strerror(int argc)
{
        if (argc != 1) {
                vm_panic("curl::strerror() expects 1 argument but got %d", argc);
        }

        struct value n = ARG(0);

        if (n.type != VALUE_INTEGER) {
                vm_panic("the argument to curl::strerror() must be an integer");
        }


        char const *msg = curl_easy_strerror(n.integer);

        return STRING_NOGC(msg, strlen(msg));
}
