#include <curl/curl.h>

#include "value.h"
#include "alloc.h"
#include "vec.h"
#include "vm.h"
#include "table.h"
#include "object.h"
#include "util.h"

static vec(char) response;

static size_t
write_function(char *ptr, size_t size, size_t nmemb, void *data)
{
        size_t n = size * nmemb;

        vec_push_n(response, ptr, n);

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
        
        vec_init(response);

        CURLcode r = curl_easy_perform(curl.ptr);

        if (r != CURLE_OK) {
                vec_empty(response);
                return INTEGER(r);
        }

        struct blob *b = value_blob_new();
        b->items = response.items;
        b->count = response.count;
        b->capacity = response.capacity;

        return BLOB(b);
}
