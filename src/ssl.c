#include <errno.h>
#include <string.h>

#include <sys/socket.h>
#include <sys/types.h>

#include "ty.h"
#include "value.h"
#include "dict.h"
#include "vm.h"
#include "class.h"
#include "functions.h"
#include "dynlib.h"
#include "tls.h"

enum {
        SSL_ERROR_WANT_READ   = 2,
        SSL_ERROR_WANT_WRITE  = 3,
        SSL_ERROR_SYSCALL     = 5,
        SSL_ERROR_ZERO_RETURN = 6
};

enum {
        SSL_FILETYPE_PEM                = 1,
        SSL_CTRL_SET_TLSEXT_SERVERNAME_CB = 53,
        SSL_CTRL_SET_TLSEXT_HOSTNAME    = 55,
        SSL_CTRL_CHAIN_CERT             = 89,
        SSL_TLSEXT_ERR_OK               = 0,
        SSL_TLSEXT_ERR_ALERT_FATAL      = 2,
        SSL_TLSEXT_ERR_NOACK            = 3,
        TLSEXT_NAMETYPE_host_name       = 0,
        OPENSSL_NPN_NEGOTIATED          = 1,
        BIO_C_SET_BUF_MEM_EOF_RETURN    = 130,
        MBSTRING_ASC                    = 0x1001,
        NID_subject_alt_name            = 85
};

enum {
        E_BASE = -1000
};

#if defined(__APPLE__)
#define SEND_FLAGS 0
#else
#define SEND_FLAGS MSG_NOSIGNAL
#endif

typedef void *P;
typedef void const *CP;

#define SSL_FNS(X)                                                                  \
        X(int,          OPENSSL_init_ssl,                 u64, P)                   \
        X(P,            TLS_server_method,                void)                     \
        X(P,            TLS_client_method,                void)                     \
        X(P,            SSL_CTX_new,                      P)                        \
        X(void,         SSL_CTX_free,                     P)                        \
        X(long,         SSL_CTX_ctrl,                     P, int, long, P)          \
        X(long,         SSL_CTX_callback_ctrl,            P, int, void (*)(void))   \
        X(u64,          SSL_CTX_set_options,              P, u64)                   \
        X(int,          SSL_CTX_use_certificate_chain_file, P, char const *)        \
        X(int,          SSL_CTX_use_PrivateKey_file,      P, char const *, int)     \
        X(int,          SSL_CTX_use_certificate,          P, P)                     \
        X(int,          SSL_CTX_use_PrivateKey,           P, P)                     \
        X(int,          SSL_CTX_check_private_key,        P)                        \
        X(int,          SSL_CTX_set_cipher_list,          P, char const *)          \
        X(int,          SSL_CTX_set_ciphersuites,         P, char const *)          \
        X(void,         SSL_CTX_set_verify,               P, int, P)                \
        X(int,          SSL_CTX_set_default_verify_paths, P)                        \
        X(int,          SSL_CTX_load_verify_locations,    P, char const *, char const *) \
        X(void,         SSL_CTX_set_alpn_select_cb,       P, P, P)                  \
        X(int,          SSL_CTX_set_alpn_protos,          P, u8 const *, unsigned)  \
        X(int,          SSL_CTX_set_session_id_context,   P, u8 const *, unsigned)  \
        X(P,            SSL_CTX_get_cert_store,           P)                        \
        X(int,          SSL_select_next_proto,            u8 **, u8 *, u8 const *, unsigned, u8 const *, unsigned) \
        X(P,            SSL_new,                          P)                        \
        X(void,         SSL_free,                         P)                        \
        X(long,         SSL_ctrl,                         P, int, long, P)          \
        X(void,         SSL_set_accept_state,             P)                        \
        X(void,         SSL_set_connect_state,            P)                        \
        X(void,         SSL_set_bio,                      P, P, P)                  \
        X(int,          SSL_set1_host,                    P, char const *)          \
        X(P,            SSL_get0_param,                   P)                        \
        X(P,            SSL_set_SSL_CTX,                  P, P)                     \
        X(int,          SSL_do_handshake,                 P)                        \
        X(int,          SSL_is_init_finished,             P)                        \
        X(int,          SSL_read_ex,                      P, void *, size_t, size_t *) \
        X(int,          SSL_write_ex,                     P, void const *, size_t, size_t *) \
        X(int,          SSL_pending,                      P)                        \
        X(int,          SSL_get_error,                    P, int)                   \
        X(int,          SSL_shutdown,                     P)                        \
        X(char const *, SSL_get_version,                  P)                        \
        X(char const *, SSL_get_servername,               P, int)                   \
        X(P,            SSL_get_current_cipher,           P)                        \
        X(char const *, SSL_CIPHER_get_name,              P)                        \
        X(long,         SSL_get_verify_result,            P)                        \
        X(P,            SSL_get1_peer_certificate,        P)                        \
        X(void,         SSL_get0_alpn_selected,           P, u8 const **, unsigned *)

#define CRYPTO_FNS(X)                                                               \
        X(int,          X509_VERIFY_PARAM_set1_ip_asc,    P, char const *)          \
        X(P,            BIO_s_mem,                        void)                     \
        X(P,            BIO_new,                          P)                        \
        X(P,            BIO_new_mem_buf,                  void const *, int)        \
        X(int,          BIO_free,                         P)                        \
        X(int,          BIO_read,                         P, void *, int)           \
        X(int,          BIO_write,                        P, void const *, int)     \
        X(long,         BIO_ctrl,                         P, int, long, P)          \
        X(size_t,       BIO_ctrl_pending,                 P)                        \
        X(unsigned long, ERR_get_error,                   void)                     \
        X(void,         ERR_clear_error,                  void)                     \
        X(void,         ERR_error_string_n,               unsigned long, char *, size_t) \
        X(P,            PEM_read_bio_X509,                P, P, P, P)               \
        X(P,            PEM_read_bio_X509_AUX,            P, P, P, P)               \
        X(P,            PEM_read_bio_PrivateKey,          P, P, P, P)               \
        X(int,          PEM_write_bio_X509,               P, P)                     \
        X(int,          PEM_write_bio_PrivateKey,         P, P, P, P, int, P, P)    \
        X(void,         X509_free,                        P)                        \
        X(int,          X509_STORE_add_cert,              P, P)                     \
        X(P,            X509_new,                         void)                     \
        X(int,          X509_set_version,                 P, long)                  \
        X(P,            X509_get_serialNumber,            P)                        \
        X(int,          ASN1_INTEGER_set,                 P, long)                  \
        X(P,            X509_getm_notBefore,              P)                        \
        X(P,            X509_getm_notAfter,               P)                        \
        X(P,            X509_gmtime_adj,                  P, long)                  \
        X(int,          X509_set_pubkey,                  P, P)                     \
        X(P,            X509_get_subject_name,            P)                        \
        X(int,          X509_set_issuer_name,             P, P)                     \
        X(int,          X509_NAME_add_entry_by_txt,       P, char const *, int, u8 const *, int, int, int) \
        X(char *,       X509_NAME_oneline,                P, char *, int)           \
        X(P,            X509V3_EXT_conf_nid,              P, P, int, char const *)  \
        X(int,          X509_add_ext,                     P, P, int)                \
        X(void,         X509_EXTENSION_free,              P)                        \
        X(int,          X509_sign,                        P, P, P)                  \
        X(char const *, X509_verify_cert_error_string,    long)                     \
        X(P,            EVP_sha256,                       void)                     \
        X(P,            EVP_PKEY_CTX_new_from_name,       P, char const *, char const *) \
        X(void,         EVP_PKEY_CTX_free,                P)                        \
        X(int,          EVP_PKEY_keygen_init,             P)                        \
        X(int,          EVP_PKEY_CTX_set_group_name,      P, char const *)          \
        X(int,          EVP_PKEY_generate,                P, P *)                   \
        X(void,         EVP_PKEY_free,                    P)                        \
        X(int,          RAND_bytes,                       u8 *, int)                \
        X(u8 *,         HMAC,                             P, void const *, int, u8 const *, size_t, u8 *, unsigned *)

#define X(r, f, ...) r (*f)(__VA_ARGS__);
static struct { SSL_FNS(X) CRYPTO_FNS(X) } O;
#undef X

#define X(r, f, ...) #f,
static char const *const SslNames[]    = { SSL_FNS(X) NULL };
static char const *const CryptoNames[] = { CRYPTO_FNS(X) NULL };
#undef X

static bool Loaded;
static char LoadError[256];

static void
load(void)
{
        static char const *const ssl[] = {
#if defined(__APPLE__)
                "/opt/homebrew/opt/openssl@3/lib/libssl.3.dylib",
                "/usr/local/opt/openssl@3/lib/libssl.3.dylib",
                "/opt/local/lib/libssl.3.dylib",
                "libssl.3.dylib",
#else
                "libssl.so.3",
                "libssl.so",
#endif
                NULL
        };
        static char const *const crypto[] = {
#if defined(__APPLE__)
                "/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib",
                "/usr/local/opt/openssl@3/lib/libcrypto.3.dylib",
                "/opt/local/lib/libcrypto.3.dylib",
                "libcrypto.3.dylib",
#else
                "libcrypto.so.3",
                "libcrypto.so",
#endif
                NULL
        };
        char const *missing;

        void *c = DynOpen("TY_LIBCRYPTO", crypto);
        void *s = DynOpen("TY_LIBSSL", ssl);

        if (c == NULL || s == NULL) {
                ty_snprintf(LoadError, sizeof LoadError, "failed to load %s (OpenSSL 3)", (c == NULL) ? "libcrypto" : "libssl");
                return;
        }

        if (
                !DynBind(s, (void **)&O, SslNames, &missing)
             || !DynBind(c, (void **)&O + countof(SslNames) - 1, CryptoNames, &missing)
        ) {
                ty_snprintf(LoadError, sizeof LoadError, "OpenSSL is missing %s (OpenSSL 3 is required)", missing);
                return;
        }

        O.OPENSSL_init_ssl(0, NULL);

        Loaded = true;
}

static bool
loaded(void)
{
        static TyOnce once = TY_ONCE_INIT;
        TyOnceRun(&once, load);
        return Loaded;
}

static void
need(Ty *ty, char const *ctx)
{
        if (!loaded()) {
                zP("%s: %s", ctx, LoadError);
        }
}

typedef struct {
        P    ctx;
        u8  *alpn;
        int  nalpn;
} Ctx;

typedef struct tls {
        P    ssl;
        P    rbio;
        P    wbio;
        bool eof;
        bool done;
} Sess;

typedef struct {
        Ty          *ty;
        Value const *h;
        Value        exc;
        bool         failed;
} Sni;

static _Thread_local Sni *CurrentSni;

static int SniSelectId;

static void
ctx_free(void *p)
{
        Ctx *c = p;

        O.SSL_CTX_free(c->ctx);
        xmF(c->alpn);
        xmF(c);
}

static void
sess_free(void *p)
{
        Sess *s = p;

        O.SSL_free(s->ssl);
        xmF(s);
}

static Value
autoptr(Ty *ty, void *p, void (*dtor)(void *))
{
        Value *d = mAo(sizeof (Value [2]), GC_FFI_AUTO);

        d[0] = PTR((void *)dtor);
        d[1] = PTR(p);

        return GCPTR(p, d);
}

static void *
ptr_arg(Ty *ty, char const *ctx, char const *name, Value v)
{
        need(ty, ctx);

        if (v.type != VALUE_PTR || v.ptr == NULL) {
                TyBuiltinBadArg(ty, ctx, name, "Ptr", &v);
        }

        return v.ptr;
}

#define CTX(v)  ((Ctx  *)ptr_arg(ty, _name__, "ctx", (v)))
#define SESS(v) ((Sess *)ptr_arg(ty, _name__, "s",   (v)))

static void
bytes_arg(Ty *ty, char const *ctx, char const *name, Value v, u8 const **p, usize *n)
{
        switch (v.type) {
        case VALUE_BLOB:
                *p = vv(*v.blob);
                *n = vN(*v.blob);
                break;

        case VALUE_STRING:
                *p = (u8 const *)ss(v);
                *n = sN(v);
                break;

        default:
                TyBuiltinBadArg(ty, ctx, name, "String | Blob", &v);
        }
}

static char *
zstr(Ty *ty, Value v)
{
        char *z = smA(sN(v) + 1);

        memcpy(z, ss(v), sN(v));
        z[sN(v)] = '\0';

        return z;
}

static char *
cstr(Ty *ty, Value v)
{
        return (v.type == VALUE_STRING) ? zstr(ty, v) : NULL;
}

static P
mem_bio(Ty *ty, char const *ctx, Value pem)
{
        u8 const *p;
        usize n;

        bytes_arg(ty, ctx, "pem", pem, &p, &n);

        return O.BIO_new_mem_buf(p, n);
}

static Value
bio_string(Ty *ty, P bio)
{
        usize n = O.BIO_ctrl_pending(bio);
        char *buf = xmA(max(n, 1));
        int got = O.BIO_read(bio, buf, n);
        Value s = vSs(buf, max(got, 0));

        xmF(buf);

        return s;
}

static int
alpn_select(P ssl, u8 const **out, u8 *outlen, u8 const *client, unsigned nclient, void *arg)
{
        Ctx *c = arg;

        int rc = O.SSL_select_next_proto((u8 **)out, outlen, c->alpn, c->nalpn, client, nclient);

        return (rc == OPENSSL_NPN_NEGOTIATED) ? SSL_TLSEXT_ERR_OK : SSL_TLSEXT_ERR_NOACK;
}

static int
sni_select(P ssl, int *alert, void *arg)
{
        Sni *sni = CurrentSni;
        char const *name = O.SSL_get_servername(ssl, TLSEXT_NAMETYPE_host_name);

        if (name == NULL || sni == NULL || sni->failed || sni->h == NULL || sni->h->type != VALUE_OBJECT) {
                return SSL_TLSEXT_ERR_OK;
        }

        Ty *ty = sni->ty;
        Value *f = class_lookup_method_i(ty, sni->h->class, SniSelectId);

        if (f == NULL) {
                return SSL_TLSEXT_ERR_OK;
        }

        if (TY_CATCH_ERROR()) {
                sni->exc    = TY_CATCH();
                sni->failed = true;
                return SSL_TLSEXT_ERR_ALERT_FATAL;
        }

        Value host = vSsz(name);
        vmP(&host);
        Value r = vm_call_method(ty, sni->h, f, 1);

        TY_CATCH_END();

        if (r.type == VALUE_PTR && r.ptr != NULL) {
                O.SSL_set_SSL_CTX(ssl, ((Ctx *)r.ptr)->ctx);
        }

        return SSL_TLSEXT_ERR_OK;
}

// _ssl.available?() -> Bool
TY_BUILTIN(ssl_available)
{
        return BOOLEAN(loaded());
}

// _ssl.load-error() -> String | nil
TY_BUILTIN(ssl_load_error)
{
        return loaded() ? NIL : vSsz(LoadError);
}

// _ssl.errors() -> Array[String]
TY_BUILTIN(ssl_errors)
{
        Value out = ARRAY(vA());
        char buf[256];
        unsigned long e;

        if (!loaded()) {
                return out;
        }

        gP(&out);
        while ((e = O.ERR_get_error()) != 0) {
                O.ERR_error_string_n(e, buf, sizeof buf);
                vAp(out.array, vSsz(buf));
        }
        gX();

        return out;
}

// _ssl.clear-errors() -> nil
TY_BUILTIN(ssl_clear_errors)
{
        if (loaded()) {
                O.ERR_clear_error();
        }

        return NIL;
}

// _ssl.verify-error(n: Int) -> String
TY_BUILTIN(ssl_verify_error)
{
        need(ty, _name__);
        return vSsz(O.X509_verify_cert_error_string(n));
}

// _ssl.ctx-new(server: Bool) -> Ptr | nil
TY_BUILTIN(ssl_ctx_new)
{
        need(ty, _name__);

        P ctx = O.SSL_CTX_new(server ? O.TLS_server_method() : O.TLS_client_method());

        if (ctx == NULL) {
                return NIL;
        }

        Ctx *c = xmA(sizeof *c);
        *c = (Ctx) { .ctx = ctx };

        return autoptr(ty, c, ctx_free);
}

// _ssl.ctx-ctrl(ctx: Ptr, cmd: Int, larg: Int) -> Int
TY_BUILTIN(ssl_ctx_ctrl)
{
        return INTEGER(O.SSL_CTX_ctrl(CTX(ctx)->ctx, cmd, larg, NULL));
}

// _ssl.ctx-options(ctx: Ptr, op: Int) -> Int
TY_BUILTIN(ssl_ctx_options)
{
        return INTEGER(O.SSL_CTX_set_options(CTX(ctx)->ctx, op));
}

// _ssl.ctx-cipher-list(ctx: Ptr, s: String) -> Int
TY_BUILTIN(ssl_ctx_cipher_list)
{
        Ctx *c = CTX(ctx);
        SCRATCH_SAVE();
        int rc = O.SSL_CTX_set_cipher_list(c->ctx, zstr(ty, s));
        SCRATCH_RESTORE();
        return INTEGER(rc);
}

// _ssl.ctx-ciphersuites(ctx: Ptr, s: String) -> Int
TY_BUILTIN(ssl_ctx_ciphersuites)
{
        Ctx *c = CTX(ctx);
        SCRATCH_SAVE();
        int rc = O.SSL_CTX_set_ciphersuites(c->ctx, zstr(ty, s));
        SCRATCH_RESTORE();
        return INTEGER(rc);
}

// _ssl.ctx-session-id(ctx: Ptr, id: String) -> Int
TY_BUILTIN(ssl_ctx_session_id)
{
        Ctx *c = CTX(ctx);
        return INTEGER(O.SSL_CTX_set_session_id_context(c->ctx, (u8 const *)ss(id), sN(id)));
}

// _ssl.ctx-cert-pem(ctx: Ptr, pem: String | Blob) -> String | nil
TY_BUILTIN(ssl_ctx_cert_pem)
{
        Ctx *c = CTX(ctx);
        P bio = mem_bio(ty, _name__, pem);
        char const *err = NULL;

        if (bio == NULL) {
                return vSsz("BIO_new_mem_buf");
        }

        P x509 = O.PEM_read_bio_X509_AUX(bio, NULL, NULL, NULL);

        if (x509 == NULL) {
                err = "ssl: invalid certificate PEM";
                goto End;
        }

        int rc = O.SSL_CTX_use_certificate(c->ctx, x509);
        O.X509_free(x509);

        if (rc != 1) {
                err = "SSL_CTX_use_certificate";
                goto End;
        }

        while ((x509 = O.PEM_read_bio_X509(bio, NULL, NULL, NULL)) != NULL) {
                long ok = O.SSL_CTX_ctrl(c->ctx, SSL_CTRL_CHAIN_CERT, 1, x509);
                O.X509_free(x509);
                if (ok != 1) {
                        err = "SSL_CTX_add1_chain_cert";
                        goto End;
                }
        }

        O.ERR_clear_error();

End:
        O.BIO_free(bio);

        return (err == NULL) ? NIL : vSsz(err);
}

// _ssl.ctx-cert-file(ctx: Ptr, path: String) -> Int
TY_BUILTIN(ssl_ctx_cert_file)
{
        Ctx *c = CTX(ctx);
        SCRATCH_SAVE();
        int rc = O.SSL_CTX_use_certificate_chain_file(c->ctx, zstr(ty, path));
        SCRATCH_RESTORE();
        return INTEGER(rc);
}

// _ssl.ctx-key-pem(ctx: Ptr, pem: String | Blob) -> String | nil
TY_BUILTIN(ssl_ctx_key_pem)
{
        Ctx *c = CTX(ctx);
        P bio = mem_bio(ty, _name__, pem);

        if (bio == NULL) {
                return vSsz("BIO_new_mem_buf");
        }

        P pkey = O.PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);
        O.BIO_free(bio);

        if (pkey == NULL) {
                return vSsz("ssl: invalid private key PEM");
        }

        int rc = O.SSL_CTX_use_PrivateKey(c->ctx, pkey);
        O.EVP_PKEY_free(pkey);

        return (rc == 1) ? NIL : vSsz("SSL_CTX_use_PrivateKey");
}

// _ssl.ctx-key-file(ctx: Ptr, path: String) -> Int
TY_BUILTIN(ssl_ctx_key_file)
{
        Ctx *c = CTX(ctx);
        SCRATCH_SAVE();
        int rc = O.SSL_CTX_use_PrivateKey_file(c->ctx, zstr(ty, path), SSL_FILETYPE_PEM);
        SCRATCH_RESTORE();
        return INTEGER(rc);
}

// _ssl.ctx-check-key(ctx: Ptr) -> Int
TY_BUILTIN(ssl_ctx_check_key)
{
        return INTEGER(O.SSL_CTX_check_private_key(CTX(ctx)->ctx));
}

// _ssl.ctx-ca-pem(ctx: Ptr, pem: String | Blob) -> String | nil
TY_BUILTIN(ssl_ctx_ca_pem)
{
        Ctx *c = CTX(ctx);
        P bio = mem_bio(ty, _name__, pem);
        P store = O.SSL_CTX_get_cert_store(c->ctx);
        P x509;
        int n = 0;

        if (bio == NULL) {
                return vSsz("BIO_new_mem_buf");
        }

        while ((x509 = O.PEM_read_bio_X509(bio, NULL, NULL, NULL)) != NULL) {
                int rc = O.X509_STORE_add_cert(store, x509);
                O.X509_free(x509);
                if (rc != 1) {
                        O.BIO_free(bio);
                        return vSsz("X509_STORE_add_cert");
                }
                n += 1;
        }

        O.BIO_free(bio);
        O.ERR_clear_error();

        return (n > 0) ? NIL : vSsz("ssl: no certificates found in CA PEM");
}

// _ssl.ctx-verify-locations(ctx: Ptr, file: String | nil, dir: String | nil) -> Int
TY_BUILTIN(ssl_ctx_verify_locations)
{
        Ctx *c = CTX(ctx);
        SCRATCH_SAVE();
        int rc = O.SSL_CTX_load_verify_locations(c->ctx, cstr(ty, file), cstr(ty, dir));
        SCRATCH_RESTORE();
        return INTEGER(rc);
}

// _ssl.ctx-default-verify(ctx: Ptr) -> Int
TY_BUILTIN(ssl_ctx_default_verify)
{
        return INTEGER(O.SSL_CTX_set_default_verify_paths(CTX(ctx)->ctx));
}

// _ssl.ctx-verify(ctx: Ptr, mode: Int) -> nil
TY_BUILTIN(ssl_ctx_verify)
{
        O.SSL_CTX_set_verify(CTX(ctx)->ctx, mode, NULL);
        return NIL;
}

// _ssl.ctx-alpn(ctx: Ptr, wire: Blob, server: Bool) -> Int
TY_BUILTIN(ssl_ctx_alpn)
{
        Ctx *c = CTX(ctx);

        if (!server) {
                return INTEGER(O.SSL_CTX_set_alpn_protos(c->ctx, vv(*wire), vN(*wire)));
        }

        xmF(c->alpn);
        c->alpn  = xmA(max(vN(*wire), 1));
        c->nalpn = vN(*wire);
        memcpy(c->alpn, vv(*wire), vN(*wire));

        O.SSL_CTX_set_alpn_select_cb(c->ctx, (P)alpn_select, c);

        return INTEGER(0);
}

// _ssl.ctx-sni(ctx: Ptr) -> nil
TY_BUILTIN(ssl_ctx_sni)
{
        Ctx *c = CTX(ctx);

        SniSelectId = M_ID("sniSelect");
        O.SSL_CTX_callback_ctrl(c->ctx, SSL_CTRL_SET_TLSEXT_SERVERNAME_CB, (void (*)(void))sni_select);

        return NIL;
}

static Sess *
sess_new(Ctx *c, bool server, char const *host, bool ip)
{
        P ssl = O.SSL_new(c->ctx);

        if (ssl == NULL) {
                return NULL;
        }

        if (server) {
                O.SSL_set_accept_state(ssl);
        } else {
                O.SSL_set_connect_state(ssl);
                if (host != NULL && ip) {
                        O.X509_VERIFY_PARAM_set1_ip_asc(O.SSL_get0_param(ssl), host);
                } else if (host != NULL) {
                        O.SSL_ctrl(ssl, SSL_CTRL_SET_TLSEXT_HOSTNAME, TLSEXT_NAMETYPE_host_name, (void *)host);
                        O.SSL_set1_host(ssl, host);
                }
        }

        P rbio = O.BIO_new(O.BIO_s_mem());
        P wbio = O.BIO_new(O.BIO_s_mem());

        if (rbio == NULL || wbio == NULL) {
                if (rbio != NULL) { O.BIO_free(rbio); }
                if (wbio != NULL) { O.BIO_free(wbio); }
                O.SSL_free(ssl);
                return NULL;
        }

        O.BIO_ctrl(rbio, BIO_C_SET_BUF_MEM_EOF_RETURN, -1, NULL);
        O.BIO_ctrl(wbio, BIO_C_SET_BUF_MEM_EOF_RETURN, -1, NULL);
        O.SSL_set_bio(ssl, rbio, wbio);

        Sess *x = xmA(sizeof *x);
        *x = (Sess) { .ssl = ssl, .rbio = rbio, .wbio = wbio };

        return x;
}

// _ssl.new(ctx: Ptr, server: Bool, host: String | nil = nil, ip: Bool = false) -> Ptr | nil
TY_BUILTIN(ssl_new)
{
        Ctx *c = CTX(ctx);

        SCRATCH_SAVE();
        Sess *x = sess_new(c, server, cstr(ty, host), ip);
        SCRATCH_RESTORE();

        return (x == NULL) ? NIL : autoptr(ty, x, sess_free);
}

// _ssl.feed(s: Ptr, data: Any, n: Int) -> Int
TY_BUILTIN(ssl_feed)
{
        Sess *x = SESS(s);
        void const *p;

        switch (data.type) {
        case VALUE_PTR:    p = data.ptr;          break;
        case VALUE_BLOB:   p = vv(*data.blob);    break;
        case VALUE_STRING: p = ss(data);          break;
        default:           TyBuiltinBadArg(ty, _name__, "data", "Blob | String | Ptr", &data);
        }

        if (data.type == VALUE_BLOB && n > vN(*data.blob)) {
                bP("n is larger than the blob");
        }

        if (data.type == VALUE_STRING && n > sN(data)) {
                bP("n is larger than the string");
        }

        return INTEGER((n == 0) ? 0 : O.BIO_write(x->rbio, p, n));
}

// _ssl.feed-eof(s: Ptr) -> nil
TY_BUILTIN(ssl_feed_eof)
{
        O.BIO_ctrl(SESS(s)->rbio, BIO_C_SET_BUF_MEM_EOF_RETURN, 0, NULL);
        return NIL;
}

// _ssl.handshake(s: Ptr, h: Any) -> Int
TY_BUILTIN(ssl_handshake)
{
        Sess *x = SESS(s);

        if (x->done) {
                return INTEGER(1);
        }

        Sni sni   = { .ty = ty, .h = &h, .exc = NIL };
        Sni *prev = CurrentSni;

        O.ERR_clear_error();

        CurrentSni = &sni;
        int rc = O.SSL_do_handshake(x->ssl);
        CurrentSni = prev;

        if (sni.failed) {
                vmE(&sni.exc);
        }

        if (rc == 1) {
                x->done = true;
                return INTEGER(1);
        }

        int e = O.SSL_get_error(x->ssl, rc);

        return INTEGER((e == SSL_ERROR_WANT_READ || e == SSL_ERROR_WANT_WRITE) ? 0 : -e);
}

// _ssl.done?(s: Ptr) -> Bool
TY_BUILTIN(ssl_done)
{
        Sess *x = SESS(s);
        return BOOLEAN(x->done || (x->done = (O.SSL_is_init_finished(x->ssl) == 1)));
}

// _ssl.eof?(s: Ptr) -> Bool
TY_BUILTIN(ssl_eof)
{
        return BOOLEAN(SESS(s)->eof);
}

// _ssl.verify-result(s: Ptr) -> Int
TY_BUILTIN(ssl_verify_result)
{
        return INTEGER(O.SSL_get_verify_result(SESS(s)->ssl));
}

// _ssl.read(s: Ptr, out: Blob, at: Int, max: Int, trim: Bool) -> Int
TY_BUILTIN(ssl_read)
{
        Sess *x = SESS(s);
        isize total = 0;
        size_t got;
        int r;

        if (at < 0 || at > vN(*out) || max < 0) {
                bP("bad range");
        }

        O.ERR_clear_error();

        vvR(*out, at + max);

        if (vN(*out) < at + max) {
                memset(vv(*out) + vN(*out), 0, at + max - vN(*out));
                vN(*out) = at + max;
        }

        while (total < max) {
                if (O.SSL_read_ex(x->ssl, vv(*out) + at + total, max - total, &got) == 1) {
                        total += got;
                        continue;
                }

                int e = O.SSL_get_error(x->ssl, 0);

                switch (e) {
                case SSL_ERROR_WANT_READ:
                case SSL_ERROR_WANT_WRITE:
                        r = total;
                        goto End;

                case SSL_ERROR_ZERO_RETURN:
                case SSL_ERROR_SYSCALL:
                        x->eof = true;
                        r = (total > 0) ? total : -1;
                        goto End;

                default:
                        r = E_BASE - e;
                        goto End;
                }
        }

        r = total;

End:
        if (trim) {
                vN(*out) = at + total;
        }

        return INTEGER(r);
}

// _ssl.write(s: Ptr, data: Any, off: Int, n: Int) -> Int
TY_BUILTIN(ssl_write)
{
        Sess *x = SESS(s);
        u8 const *p;
        isize done = 0;
        size_t got;

        switch (data.type) {
        case VALUE_PTR:
                p = data.ptr;
                break;

        case VALUE_BLOB:
                if (off < 0 || n < 0 || off + n > vN(*data.blob)) {
                        bP("bad range");
                }
                p = vv(*data.blob);
                break;

        case VALUE_STRING:
                if (off < 0 || n < 0 || off + n > sN(data)) {
                        bP("bad range");
                }
                p = (u8 const *)ss(data);
                break;

        default:
                TyBuiltinBadArg(ty, _name__, "data", "Blob | String | Ptr", &data);
        }

        p += off;

        O.ERR_clear_error();

        while (done < n) {
                if (O.SSL_write_ex(x->ssl, p + done, n - done, &got) == 1) {
                        done += got;
                        continue;
                }
                int e = O.SSL_get_error(x->ssl, 0);
                if (e == SSL_ERROR_WANT_READ || e == SSL_ERROR_WANT_WRITE) {
                        break;
                }
                return INTEGER(E_BASE - e);
        }

        return INTEGER(done);
}

// _ssl.pending(s: Ptr) -> Int
TY_BUILTIN(ssl_pending)
{
        return INTEGER(O.BIO_ctrl_pending(SESS(s)->wbio));
}

// _ssl.buffered(s: Ptr) -> Int
TY_BUILTIN(ssl_buffered)
{
        return INTEGER(O.SSL_pending(SESS(s)->ssl));
}

// _ssl.drain(s: Ptr, out: Blob) -> Int
TY_BUILTIN(ssl_drain)
{
        Sess *x = SESS(s);
        usize n = O.BIO_ctrl_pending(x->wbio);

        if (n == 0) {
                return INTEGER(0);
        }

        vvR(*out, vN(*out) + n);
        int got = O.BIO_read(x->wbio, vZ(*out), n);
        vN(*out) += max(got, 0);

        return INTEGER(max(got, 0));
}

// _ssl.send-to(s: Ptr, fd: Int) -> Int
TY_BUILTIN(ssl_send_to)
{
        Sess *x = SESS(s);
        u8 buf[1 << 14];
        int err = 0;

        for (;;) {
                int n = O.BIO_read(x->wbio, buf, sizeof buf);
                if (n <= 0) {
                        break;
                }
                for (int off = 0; off < n;) {
                        UnlockTy();
                        isize k = send(fd, buf + off, n - off, SEND_FLAGS);
                        err = errno;
                        LockTy();
                        if (k < 0 && err == EINTR) {
                                continue;
                        }
                        if (k < 0) {
                                return INTEGER(-err);
                        }
                        off += k;
                }
        }

        return INTEGER(0);
}

// _ssl.recv-from(s: Ptr, fd: Int) -> Int
TY_BUILTIN(ssl_recv_from)
{
        Sess *x = SESS(s);
        u8 buf[1 << 14];

        for (;;) {
                UnlockTy();
                isize n = recv(fd, buf, sizeof buf, 0);
                int err = errno;
                LockTy();
                if (n > 0) {
                        O.BIO_write(x->rbio, buf, n);
                        return INTEGER(n);
                }
                if (n == 0) {
                        return INTEGER(0);
                }
                if (err != EINTR) {
                        return INTEGER(-err);
                }
        }
}

// _ssl.shutdown(s: Ptr) -> nil
TY_BUILTIN(ssl_shutdown)
{
        Sess *x = SESS(s);

        O.ERR_clear_error();
        if (x->done || O.SSL_is_init_finished(x->ssl) == 1) {
                O.SSL_shutdown(x->ssl);
        }
        O.ERR_clear_error();

        return NIL;
}

// _ssl.alpn(s: Ptr) -> String | nil
TY_BUILTIN(ssl_alpn)
{
        u8 const *data = NULL;
        unsigned n = 0;

        O.SSL_get0_alpn_selected(SESS(s)->ssl, &data, &n);

        return (n == 0) ? NIL : vSs((char const *)data, n);
}

// _ssl.version(s: Ptr) -> String
TY_BUILTIN(ssl_version)
{
        return vSsz(O.SSL_get_version(SESS(s)->ssl));
}

// _ssl.cipher(s: Ptr) -> String | nil
TY_BUILTIN(ssl_cipher)
{
        P cipher = O.SSL_get_current_cipher(SESS(s)->ssl);
        return (cipher == NULL) ? NIL : vSsz(O.SSL_CIPHER_get_name(cipher));
}

// _ssl.server-name(s: Ptr) -> String | nil
TY_BUILTIN(ssl_server_name)
{
        char const *name = O.SSL_get_servername(SESS(s)->ssl, TLSEXT_NAMETYPE_host_name);
        return (name == NULL) ? NIL : vSsz(name);
}

// _ssl.peer(s: Ptr) -> String | nil
TY_BUILTIN(ssl_peer)
{
        P x509 = O.SSL_get1_peer_certificate(SESS(s)->ssl);
        char buf[512];

        if (x509 == NULL) {
                return NIL;
        }

        O.X509_NAME_oneline(O.X509_get_subject_name(x509), buf, sizeof buf);
        O.X509_free(x509);

        return vSsz(buf);
}

// _ssl.self-signed(cn: String, days: Int, san: String, serial: Int) -> (String, String) | String
TY_BUILTIN(ssl_self_signed)
{
        need(ty, _name__);

        char const *err = NULL;
        P pkey = NULL;
        P x509 = NULL;
        P cbio = NULL;
        P kbio = NULL;
        P kctx;

        O.ERR_clear_error();

        SCRATCH_SAVE();
        char *zcn  = zstr(ty, cn);
        char *zsan = zstr(ty, san);

        if ((kctx = O.EVP_PKEY_CTX_new_from_name(NULL, "EC", NULL)) == NULL) {
                SCRATCH_RESTORE();
                return vSsz("EVP_PKEY_CTX_new_from_name");
        }

        if (
                (O.EVP_PKEY_keygen_init(kctx) != 1)
             || (O.EVP_PKEY_CTX_set_group_name(kctx, "P-256") != 1)
             || (O.EVP_PKEY_generate(kctx, &pkey) != 1)
        ) {
                err = "EVP_PKEY_generate";
                goto End;
        }

        x509 = O.X509_new();
        O.X509_set_version(x509, 2);
        O.ASN1_INTEGER_set(O.X509_get_serialNumber(x509), serial & 0x7FFFFFFF);
        O.X509_gmtime_adj(O.X509_getm_notBefore(x509), -3600);
        O.X509_gmtime_adj(O.X509_getm_notAfter(x509), days * 86400);
        O.X509_set_pubkey(x509, pkey);

        P name = O.X509_get_subject_name(x509);
        O.X509_NAME_add_entry_by_txt(name, "CN", MBSTRING_ASC, (u8 const *)zcn, -1, -1, 0);
        O.X509_set_issuer_name(x509, name);

        if (sN(san) > 0) {
                P ext = O.X509V3_EXT_conf_nid(NULL, NULL, NID_subject_alt_name, zsan);
                if (ext == NULL) {
                        err = "X509V3_EXT_conf_nid";
                        goto End;
                }
                O.X509_add_ext(x509, ext, -1);
                O.X509_EXTENSION_free(ext);
        }

        if (O.X509_sign(x509, pkey, O.EVP_sha256()) == 0) {
                err = "X509_sign";
                goto End;
        }

        cbio = O.BIO_new(O.BIO_s_mem());
        kbio = O.BIO_new(O.BIO_s_mem());

        O.PEM_write_bio_X509(cbio, x509);
        O.PEM_write_bio_PrivateKey(kbio, pkey, NULL, NULL, 0, NULL, NULL);

        Value pair = vT(2);
        gP(&pair);
        pair.items[0] = bio_string(ty, cbio);
        pair.items[1] = bio_string(ty, kbio);
        gX();

        O.BIO_free(cbio);
        O.BIO_free(kbio);
        O.X509_free(x509);
        O.EVP_PKEY_free(pkey);
        O.EVP_PKEY_CTX_free(kctx);
        SCRATCH_RESTORE();

        return pair;

End:
        if (x509 != NULL) { O.X509_free(x509);     }
        if (pkey != NULL) { O.EVP_PKEY_free(pkey); }
        O.EVP_PKEY_CTX_free(kctx);
        SCRATCH_RESTORE();

        return vSsz(err);
}

// _ssl.random-bytes(n: Int) -> Blob | nil
TY_BUILTIN(ssl_random_bytes)
{
        need(ty, _name__);

        if (n < 0 || n > INT_MAX) {
                bP("bad size: %"PRIi64, n);
        }

        Blob *out = value_blob_new(ty);
        Value result = BLOB(out);

        gP(&result);
        vvR(*out, max(n, 1));
        gX();

        if (n > 0 && O.RAND_bytes(vv(*out), n) != 1) {
                return NIL;
        }

        vN(*out) = n;

        return result;
}

// _ssl.hmac-sha256(key: String | Blob, data: String | Blob) -> Blob | nil
TY_BUILTIN(ssl_hmac_sha256)
{
        need(ty, _name__);

        u8 const *k;
        u8 const *d;
        usize nk;
        usize nd;
        u8 md[32];
        unsigned n = 0;

        bytes_arg(ty, _name__, "key",  key,  &k, &nk);
        bytes_arg(ty, _name__, "data", data, &d, &nd);

        if (O.HMAC(O.EVP_sha256(), k, nk, d, nd, md, &n) == NULL) {
                return NIL;
        }

        Blob *out = value_blob_new(ty);
        vvPn(*out, md, n);

        return BLOB(out);
}

// _ssl.equal?(a: String | Blob, b: String | Blob) -> Bool
TY_BUILTIN(ssl_equal)
{
        u8 const *x;
        u8 const *y;
        usize nx;
        usize ny;
        u8 acc = 0;

        bytes_arg(ty, _name__, "a", a, &x, &nx);
        bytes_arg(ty, _name__, "b", b, &y, &ny);

        if (nx != ny) {
                return BOOLEAN(false);
        }

        for (usize i = 0; i < nx; ++i) {
                acc |= x[i] ^ y[i];
        }

        return BOOLEAN(acc == 0);
}

#undef SESS
#undef CTX

bool
TlsLoad(char const **why)
{
        if (!loaded()) {
                *why = LoadError;
                return false;
        }

        return true;
}

Tls *
TlsNew(void *ctx, bool server, char const *host)
{
        bool ip = (host != NULL) && (strchr(host, ':') != NULL || strspn(host, "0123456789.") == strlen(host));
        return loaded() ? sess_new(ctx, server, host, ip) : NULL;
}

void
TlsFree(Tls *t)
{
        if (t != NULL) {
                sess_free(t);
        }
}

int
TlsHandshake(Ty *ty, Tls *t, Value const *h)
{
        if (t->done) {
                return 1;
        }

        Sni sni   = { .ty = ty, .h = h, .exc = NIL };
        Sni *prev = CurrentSni;

        O.ERR_clear_error();

        CurrentSni = &sni;
        int rc = O.SSL_do_handshake(t->ssl);
        CurrentSni = prev;

        if (sni.failed) {
                return -1;
        }

        if (rc == 1) {
                t->done = true;
                return 1;
        }

        int e = O.SSL_get_error(t->ssl, rc);

        return (e == SSL_ERROR_WANT_READ || e == SSL_ERROR_WANT_WRITE) ? 0 : -e;
}

bool
TlsDone(Tls const *t)
{
        return t->done;
}

bool
TlsFeed(Tls *t, void const *p, usize n)
{
        return (n == 0) || (O.BIO_write(t->rbio, p, n) == (int)n);
}

void
TlsFeedEof(Tls *t)
{
        O.BIO_ctrl(t->rbio, BIO_C_SET_BUF_MEM_EOF_RETURN, 0, NULL);
}

isize
TlsRead(Tls *t, void *p, usize n)
{
        size_t got;

        O.ERR_clear_error();

        if (O.SSL_read_ex(t->ssl, p, n, &got) == 1) {
                return got;
        }

        switch (O.SSL_get_error(t->ssl, 0)) {
        case SSL_ERROR_WANT_READ:
        case SSL_ERROR_WANT_WRITE:
                return 0;

        case SSL_ERROR_ZERO_RETURN:
        case SSL_ERROR_SYSCALL:
                t->eof = true;
                return -1;
        }

        return -2;
}

isize
TlsWrite(Tls *t, void const *p, usize n)
{
        usize done = 0;
        size_t got;

        O.ERR_clear_error();

        while (done < n) {
                if (O.SSL_write_ex(t->ssl, (u8 const *)p + done, n - done, &got) == 1) {
                        done += got;
                        continue;
                }
                int e = O.SSL_get_error(t->ssl, 0);
                if (e == SSL_ERROR_WANT_READ || e == SSL_ERROR_WANT_WRITE) {
                        break;
                }
                return -1;
        }

        return done;
}

usize
TlsPending(Tls const *t)
{
        return O.BIO_ctrl_pending(t->wbio);
}

usize
TlsBuffered(Tls const *t)
{
        return O.SSL_pending(t->ssl);
}

isize
TlsDrain(Tls *t, void *p, usize n)
{
        int got = O.BIO_read(t->wbio, p, n);
        return max(got, 0);
}

void
TlsShutdown(Tls *t)
{
        O.ERR_clear_error();
        if (t->done || O.SSL_is_init_finished(t->ssl) == 1) {
                O.SSL_shutdown(t->ssl);
        }
        O.ERR_clear_error();
}

bool
TlsEof(Tls const *t)
{
        return t->eof;
}

bool
TlsAlpn(Tls const *t, char const **p, unsigned *n)
{
        u8 const *a = NULL;

        O.SSL_get0_alpn_selected(t->ssl, &a, n);
        *p = (char const *)a;

        return a != NULL && *n > 0;
}

long
TlsVerifyResult(Tls const *t)
{
        return O.SSL_get_verify_result(t->ssl);
}

char const *
TlsVerifyError(long r)
{
        return O.X509_verify_cert_error_string(r);
}

void
TlsErrors(char *buf, usize n)
{
        usize at = 0;
        unsigned long e;

        buf[0] = '\0';

        while ((e = O.ERR_get_error()) != 0 && at + 2 < n) {
                if (at > 0) {
                        buf[at++] = ';';
                        buf[at++] = ' ';
                }
                O.ERR_error_string_n(e, buf + at, n - at);
                at += strlen(buf + at);
        }
}

/* vim: set sts=8 sw=8 expandtab: */
