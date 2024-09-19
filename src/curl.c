#include <curl/curl.h>
#include <curl/easy.h>
#include <curl/urlapi.h>

#include "value.h"
#include "alloc.h"
#include "vec.h"
#include "vm.h"
#include "table.h"
#include "object.h"
#include "util.h"

static _Thread_local vec(char) Buffer;

static size_t
write_function(char *ptr, size_t size, size_t nmemb, void *data)
{
        Ty *ty = data;

        size_t n = size * nmemb;

        vvPn(Buffer, ptr, n);

        return n;
}

struct value
builtin_curl_free(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 0) {
                zP("curl.free(): expected 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("curl.free(): expected pointer but got: %s", value_show_color(ty, &ARG(0)));
        }

        curl_free(ARG(0).ptr);

        return NIL;
}

struct value
builtin_curl_init(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 0) {
                zP("curl::init() expects no arguments but got %d", argc);
        }

        CURL *c = curl_easy_init();
        
        if (c == NULL) {
                zP("curl_easy_init returned NULL");
        }

        if (curl_easy_setopt(c, CURLOPT_WRITEFUNCTION, write_function) != CURLE_OK) {
                zP("failed to set CURLOPT_WRITEFUNCTION");
        }

        if (curl_easy_setopt(c, CURLOPT_WRITEDATA, ty) != CURLE_OK) {
                zP("failed to set CURLOPT_WRITEDATA");
        }

        return PTR(c);
}

struct value
builtin_curl_mime(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("curl::mime::init() expects 1 argument but got %d", argc);
        }

        struct value curl = ARG(0);
        if (curl.type != VALUE_PTR) {
                zP("the first argument to curl::mime() must be a pointer");
        }

        curl_mime *m = curl_mime_init(curl.ptr);
        if (m == NULL) {
                zP("curl_mime_init returned NULL");
        }

        return PTR(m);
}

struct value
builtin_curl_mime_add(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("curl::mime::add() expects 1 argument but got %d", argc);
        }

        struct value mime = ARG(0);
        if (mime.type != VALUE_PTR) {
                zP("the first argument to curl::mime::add() must be a pointer");
        }

        curl_mimepart *p = curl_mime_addpart(mime.ptr);
        if (p == NULL) {
                zP("curl_mime_addpart returned NULL");
        }

        return PTR(p);
}

struct value
builtin_curl_mime_data(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 2) {
                zP("curl::mime::data() expects 2 arguments but got %d", argc);
        }

        struct value part = ARG(0);
        if (part.type != VALUE_PTR) {
                zP("the first argument to curl::mime::data() must be a pointer");
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
                zP("invalid data argument passed to curl::mime::data()");
        }

        return NIL;
}

struct value
builtin_curl_mime_name(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 2) {
                zP("curl::mime::name() expects 2 arguments but got %d", argc);
        }

        struct value part = ARG(0);
        if (part.type != VALUE_PTR) {
                zP("the first argument to curl::mime::name() must be a pointer");
        }

        Buffer.count = 0;

        struct value name = ARG(1);
        switch (name.type) {
        case VALUE_STRING:
                vvPn(Buffer, name.string, name.bytes);
                vvP(Buffer, '\0');
                break;
        case VALUE_BLOB:
                vvPn(Buffer, name.blob->items, name.blob->count);
                vvP(Buffer, '\0');
                break;
        default:
                zP("invalid name argument passed to curl::mime::name()");
        }

        curl_mime_name(part.ptr, name.string);

        return NIL;
}

struct value
builtin_curl_slist_append(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 2) {
                zP("curl::slist::append() expects 2 arguments but got %d", argc);
        }

        struct value slist = ARG(0);
        if (slist.type != VALUE_PTR) {
                zP("the first argument to curl::slist::append() must be a pointer");
        }

        struct value s = ARG(1);
        if (s.type != VALUE_BLOB) {
                zP("the second argument to curl::slist::append() must be a blob");
        }

        struct curl_slist *list = curl_slist_append(slist.ptr, s.blob->items);
        if (list == NULL) {
                zP("out of memory");
        }

        return PTR(list);
}

struct value
builtin_curl_slist_free(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("curl::slist::free() expects 1 argument but got %d", argc);
        }

        struct value slist = ARG(0);
        if (slist.type != VALUE_PTR) {
                zP("the argument to curl::slist::free() must be a pointer");
        }

        curl_slist_free_all(slist.ptr);

        return NIL;
}

struct value
builtin_curl_getinfo(Ty *ty, int argc, struct value *kwargs)
{
        if (argc < 2) {
                zP("curl::getinfo() expects at least 2 arguments but got %d", argc);
        }

        struct value curl = ARG(0);
        if (curl.type != VALUE_PTR) {
                zP("the first argument to curl::getinfo() must be a pointer");
        }

        struct value opt = ARG(1);
        if (opt.type != VALUE_INTEGER) {
                zP("the second argument to curl::getinfo() must be an integer");
        }

        struct value s;
        char buffer[1024];

        long rc;

        switch (opt.integer) {
        case CURLINFO_RESPONSE_CODE:
                curl_easy_getinfo(curl.ptr, CURLINFO_RESPONSE_CODE, &rc);
                return INTEGER(rc);
        default:
                return NIL;
        }
}

struct value
builtin_curl_setopt(Ty *ty, int argc, struct value *kwargs)
{
        if (argc < 2) {
                zP("curl::setopt() expects at least 2 arguments but got %d", argc);
        }

        struct value curl = ARG(0);
        if (curl.type != VALUE_PTR) {
                zP("the first argument to curl::setopt() must be a pointer");
        }

        struct value opt = ARG(1);
        if (opt.type != VALUE_INTEGER) {
                zP("the second argument to curl::setopt() must be an integer");
        }

        struct value s;
        char buffer[1024];

        switch (opt.integer) {
        case CURLOPT_URL:
                s = ARG(2);
                if (s.type != VALUE_STRING) {
                        zP("the value of CURLOPT_URL must be a string");
                }
                if (s.bytes >= sizeof buffer) {
                        zP("CURLOPT_URL is too long");
                }
                memcpy(buffer, s.string, s.bytes);
                buffer[s.bytes] = '\0';
                return INTEGER(curl_easy_setopt(curl.ptr, CURLOPT_URL, buffer));
        case CURLOPT_POST:
                s = ARG(2);
                if (s.type != VALUE_INTEGER) {
                        zP("the value of CURLOPT_POST must be an integer");
                }
                curl_easy_setopt(curl.ptr, CURLOPT_POST, (long)s.integer);
                break;
        case CURLOPT_POSTFIELDS:
        case CURLOPT_COPYPOSTFIELDS:
                s = ARG(2);
                switch (s.type) {
                case VALUE_BLOB:
                        curl_easy_setopt(curl.ptr, CURLOPT_POSTFIELDSIZE, (long)s.blob->count);
                        curl_easy_setopt(curl.ptr, opt.integer, s.blob->items);
                        break;
                case VALUE_STRING:
                        curl_easy_setopt(curl.ptr, CURLOPT_POSTFIELDSIZE, (long)s.bytes);
                        curl_easy_setopt(curl.ptr, opt.integer, s.string);
                        break;
                case VALUE_PTR:
                        if (argc > 3 && ARG(3).type == VALUE_INTEGER) {
                                curl_easy_setopt(curl.ptr, CURLOPT_POSTFIELDSIZE, (long)ARG(3).integer);
                        } else {
                                curl_easy_setopt(curl.ptr, CURLOPT_POSTFIELDSIZE, -1L);
                        }
                        curl_easy_setopt(curl.ptr, opt.integer, s.ptr);
                        break;
                default:
                        zP("the value for the CURLOPT_POSTFIELDS option must be a string, a blob, or a pointer");
                }
                break;
        case CURLOPT_MIMEPOST:
                s = ARG(2);
                if (s.type != VALUE_PTR) {
                        zP("the value of CURLOPT_MIMEPOST must be a pointer");
                }
                curl_easy_setopt(curl.ptr, CURLOPT_MIMEPOST, s.ptr);
                break;
        case CURLOPT_HTTPHEADER:
                s = ARG(2);
                if (s.type != VALUE_PTR) {
                        zP("the value of CURLOPT_HTTPHEADER must be an pointer");
                }
                curl_easy_setopt(curl.ptr, CURLOPT_HTTPHEADER, s.ptr);
                break;
        case CURLOPT_FOLLOWLOCATION:
                s = ARG(2);
                if (s.type != VALUE_BOOLEAN) {
                        zP("the value of CURLOPT_FOLLOWLOCATION must be a boolean");
                }
                curl_easy_setopt(curl.ptr, CURLOPT_FOLLOWLOCATION, (long)s.boolean);
                break;
        default:
                zP("invalid option passed to curl::setopt(): %d", opt.integer);
        }

        return NIL;
}

struct value
builtin_curl_perform(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("curl::perform() expects 1 argument but got %d", argc);
        }

        struct value curl = ARG(0);
        if (curl.type != VALUE_PTR) {
                zP("the argument to curl::perform() must be a pointer");
        }
        
        vec_init(Buffer);

        CURLcode r = curl_easy_perform(curl.ptr);

        if (r != CURLE_OK) {
                vec_empty(ty, Buffer);
                return INTEGER(r);
        }

        struct blob *b = value_blob_new(ty);
        b->items = Buffer.items;
        b->count = Buffer.count;
        b->capacity = Buffer.capacity;

        vec_init(Buffer);

        return BLOB(b);
}

struct value
builtin_curl_strerror(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("curl::strerror() expects 1 argument but got %d", argc);
        }

        struct value n = ARG(0);

        if (n.type != VALUE_INTEGER) {
                zP("the argument to curl::strerror() must be an integer");
        }


        char const *msg = curl_easy_strerror(n.integer);

        return STRING_NOGC(msg, strlen(msg));
}

struct value
builtin_curl_url(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 0) {
                zP("curl.url.new(): expected no arguments but got %d", argc);
        }

        return PTR(curl_url());
}

struct value
builtin_curl_url_strerror(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("curl.url.strerror(): expected 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_INTEGER) {
                zP("curl.url.strerror(): expected integer but got: %s", value_show_color(ty, &ARG(0)));
        }
        
#if LIBCURL_VERSION_NUM >= 0x075000
        char const *s = curl_url_strerror(ARG(0).integer);
#else
        char const *s = "[curl_url_strerror not implemented]";
#endif

        return (s == NULL) ? NIL : STRING_NOGC(s, strlen(s));
}

struct value
builtin_curl_url_cleanup(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("curl.url.cleanup(): expected 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("curl.url.cleanup(): expected pointer but got: %s", value_show_color(ty, &ARG(0)));
        }

        curl_url_cleanup(ARG(0).ptr);

        return NIL;
}

struct value
builtin_curl_url_get(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 3) {
                zP("curl.url.get(): expected 4 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("curl.url.get(): expected pointer as argument 1 but got: %s", value_show_color(ty, &ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("curl.url.get(): expected integer as argument 2 but got: %s", value_show_color(ty, &ARG(1)));
        }

        if (ARG(2).type != VALUE_INTEGER) {
                zP("curl.url.get(): expected integer as argument 3 but got: %s", value_show_color(ty, &ARG(2)));
        }

        char *content;

        CURLUcode rc = curl_url_get(ARG(0).ptr, ARG(1).integer, &content, ARG(2).integer);

        if (rc != CURLUE_OK) {
                return Err(ty, INTEGER(rc));
        }

        struct value v = vSc(content, strlen(content));

        curl_free(content);

        return Ok(ty, v);
}

struct value
builtin_curl_url_set(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 4) {
                zP("curl.url.set(): expected 4 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("curl.url.set(): expected pointer as argument 1 but got: %s", value_show_color(ty, &ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("curl.url.set(): expected integer as argument 2 but got: %s", value_show_color(ty, &ARG(1)));
        }

        char const *content;

        switch (ARG(2).type) {
        case VALUE_STRING:
                Buffer.count = 0;
                vvPn(Buffer, ARG(2).string, ARG(2).bytes);
                vvP(Buffer, '\0');
                content = Buffer.items;
                break;
        case VALUE_BLOB:
                Buffer.count = 0;
                vvPn(Buffer, ARG(2).blob->items, ARG(2).blob->count);
                vvP(Buffer, '\0');
                content = Buffer.items;
                break;
        case VALUE_PTR:
                content = ARG(2).ptr;
                break;
        default:
                zP("curl.url.set(): expected string, blob, or pointer as argument 3 but got: %s", value_show_color(ty, &ARG(2)));
        }

        if (ARG(3).type != VALUE_INTEGER) {
                zP("curl.url.set(): expected integer as argument 4 but got: %s", value_show_color(ty, &ARG(3)));
        }

        return INTEGER(curl_url_set(ARG(0).ptr, ARG(1).integer, content, ARG(3).integer));
}

/* vim: set sts=8 sw=8 expandtab: */
