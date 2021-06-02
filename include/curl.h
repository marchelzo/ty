#ifndef CURL_H_INCLUDED
#define CURL_H_INCLUDED

struct value
builtin_curl_init(int argc);

struct value
builtin_curl_perform(int argc);

struct value
builtin_curl_setopt(int argc);

struct value
builtin_curl_mime(int argc);

struct value
builtin_curl_mime_add(int argc);

struct value
builtin_curl_mime_name(int argc);

struct value
builtin_curl_mime_data(int argc);

struct value
builtin_curl_slist_free(int argc);

struct value
builtin_curl_slist_append(int argc);

#endif
