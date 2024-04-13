#ifndef CURL_H_INCLUDED
#define CURL_H_INCLUDED

struct value
builtin_curl_init(int argc, struct value *kwargs);

struct value
builtin_curl_free(int argc, struct value *kwargs);

struct value
builtin_curl_perform(int argc, struct value *kwargs);

struct value
builtin_curl_strerror(int argc, struct value *kwargs);

struct value
builtin_curl_setopt(int argc, struct value *kwargs);

struct value
builtin_curl_getinfo(int argc, struct value *kwargs);

struct value
builtin_curl_mime(int argc, struct value *kwargs);

struct value
builtin_curl_mime_add(int argc, struct value *kwargs);

struct value
builtin_curl_mime_name(int argc, struct value *kwargs);

struct value
builtin_curl_mime_data(int argc, struct value *kwargs);

struct value
builtin_curl_slist_free(int argc, struct value *kwargs);

struct value
builtin_curl_slist_append(int argc, struct value *kwargs);

struct value
builtin_curl_url(int argc, struct value *kwargs);

struct value
builtin_curl_url_set(int argc, struct value *kwargs);

struct value
builtin_curl_url_get(int argc, struct value *kwargs);

struct value
builtin_curl_url_cleanup(int argc, struct value *kwargs);

struct value
builtin_curl_url_strerror(int argc, struct value *kwargs);

#endif
