#ifndef CURL_H_INCLUDED
#define CURL_H_INCLUDED

struct value
builtin_curl_init(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_free(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_perform(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_strerror(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_setopt(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_getinfo(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_mime(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_mime_add(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_mime_name(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_mime_data(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_slist_free(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_slist_append(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_url(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_url_set(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_url_get(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_url_cleanup(Ty *ty, int argc, struct value *kwargs);

struct value
builtin_curl_url_strerror(Ty *ty, int argc, struct value *kwargs);

#endif
