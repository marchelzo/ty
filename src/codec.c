#include <stdarg.h>
#include <string.h>

#include <zlib.h>
#include <zstd.h>

#include "ty.h"
#include "value.h"
#include "dict.h"
#include "vm.h"
#include "functions.h"
#include "dynlib.h"
#include "codec.h"

enum {
        CHUNK = 64 * 1024
};

enum {
        K_INFLATE,
        K_DEFLATE,
        K_BR_DEC,
        K_BR_ENC,
        K_ZSTD_DEC,
        K_ZSTD_ENC
};

enum {
        F_GZIP,
        F_ZLIB,
        F_RAW,
        F_AUTO
};

enum {
        OP_PROCESS,
        OP_FLUSH,
        OP_FINISH
};

enum {
        RUN_OK      =  0,
        RUN_ERROR   = -1,
        RUN_TOO_BIG = -2
};

enum {
        BROTLI_ERROR             = 0,
        BROTLI_SUCCESS           = 1,
        BROTLI_NEEDS_MORE_INPUT  = 2,
        BROTLI_NEEDS_MORE_OUTPUT = 3,
        BROTLI_PARAM_QUALITY     = 1,
        BROTLI_PARAM_LGWIN       = 2
};

#define BROTLI_DEC_FNS(X)                                                                         \
        X(void *,       BrotliDecoderCreateInstance,   void *, void *, void *)                    \
        X(void,         BrotliDecoderDestroyInstance,  void *)                                    \
        X(int,          BrotliDecoderDecompressStream, void *, size_t *, u8 const **, size_t *, u8 **, size_t *) \
        X(int,          BrotliDecoderGetErrorCode,     void *)                                    \
        X(char const *, BrotliDecoderErrorString,      int)

#define BROTLI_ENC_FNS(X)                                                                         \
        X(void *,       BrotliEncoderCreateInstance,   void *, void *, void *)                    \
        X(void,         BrotliEncoderDestroyInstance,  void *)                                    \
        X(int,          BrotliEncoderSetParameter,     void *, int, u32)                          \
        X(int,          BrotliEncoderCompressStream,   void *, int, size_t *, u8 const **, size_t *, u8 **, size_t *) \
        X(int,          BrotliEncoderHasMoreOutput,    void *)

#define X(r, f, ...) r (*f)(__VA_ARGS__);
static struct { BROTLI_DEC_FNS(X) } BrDec;
static struct { BROTLI_ENC_FNS(X) } BrEnc;
#undef X

#define X(r, f, ...) #f,
static char const *const BrDecNames[] = { BROTLI_DEC_FNS(X) NULL };
static char const *const BrEncNames[] = { BROTLI_ENC_FNS(X) NULL };
#undef X

static bool HaveBrDec;
static bool HaveBrEnc;

static void
brotli_load(void)
{
        static char const *const dec[] = {
#if defined(__APPLE__)
                "/opt/homebrew/lib/libbrotlidec.1.dylib",
                "/usr/local/lib/libbrotlidec.1.dylib",
                "libbrotlidec.1.dylib",
#else
                "libbrotlidec.so.1",
                "libbrotlidec.so",
#endif
                NULL
        };
        static char const *const enc[] = {
#if defined(__APPLE__)
                "/opt/homebrew/lib/libbrotlienc.1.dylib",
                "/usr/local/lib/libbrotlienc.1.dylib",
                "libbrotlienc.1.dylib",
#else
                "libbrotlienc.so.1",
                "libbrotlienc.so",
#endif
                NULL
        };
        char const *missing;

        void *d = DynOpen("TY_LIBBROTLIDEC", dec);
        void *e = DynOpen("TY_LIBBROTLIENC", enc);

        HaveBrDec = (d != NULL) && DynBind(d, (void **)&BrDec, BrDecNames, &missing);
        HaveBrEnc = (e != NULL) && DynBind(e, (void **)&BrEnc, BrEncNames, &missing);
}

static void
brotli(void)
{
        static TyOnce once = TY_ONCE_INIT;
        TyOnceRun(&once, brotli_load);
}

struct codec {
        int        kind;
        int        coding;
        int        format;
        bool       first;
        bool       end;
        bool       any;
        bool       open;
        bool       gc;
        i64        total;
        size_t     left;
        z_stream   z;
        void      *br;
        ZSTD_DCtx *zd;
        ZSTD_CCtx *zc;
        char       msg[160];
};

static void
codec_close(Codec *c)
{
        if (!c->open) {
                return;
        }

        switch (c->kind) {
        case K_INFLATE:  inflateEnd(&c->z);                         break;
        case K_DEFLATE:  deflateEnd(&c->z);                         break;
        case K_BR_DEC:   BrDec.BrotliDecoderDestroyInstance(c->br); break;
        case K_BR_ENC:   BrEnc.BrotliEncoderDestroyInstance(c->br); break;
        case K_ZSTD_DEC: ZSTD_freeDCtx(c->zd);                      break;
        case K_ZSTD_ENC: ZSTD_freeCCtx(c->zc);                      break;
        }

        c->open = false;
}

static void
codec_free(void *p)
{
        codec_close(p);
        xmF(p);
}

static int
fail(Codec *c, char const *fmt, ...)
{
        va_list ap;

        va_start(ap, fmt);
        ty_vsnprintf(c->msg, sizeof c->msg, fmt, ap);
        va_end(ap);

        codec_close(c);

        return RUN_ERROR;
}

static int
bits_of(int format)
{
        return (format == F_ZLIB) ? MAX_WBITS
             : (format == F_RAW)  ? -MAX_WBITS
             : (format == F_AUTO) ? MAX_WBITS + 32
             :                      MAX_WBITS + 16;
}

inline static u8 *
room(Ty *ty, Codec *c, CodecBytes *out, usize n)
{
        if (out->count + n > out->capacity) {
                usize cap = fit2(max(out->capacity, 256), out->count + n);
                if (c->gc) {
                        mRE(out->items, cap);
                } else {
                        mresize(out->items, cap);
                }
                out->capacity = cap;
        }

        return out->items + out->count;
}

inline static bool
grew(Codec *c, CodecBytes *out, usize n, i64 limit)
{
        out->count += n;
        c->total += n;

        return limit >= 0 && c->total > limit;
}

static int
inflate_run(Ty *ty, Codec *c, u8 const *in, usize len, CodecBytes *out, i64 limit)
{
        if (len == 0) {
                return RUN_OK;
        }

        if (c->first) {
                c->first = false;
                if (
                        (c->format == F_ZLIB)
                     && (len >= 2)
                     && (((in[0] & 0x0F) != 8) || (((in[0] << 8) | in[1]) % 31 != 0))
                ) {
                        c->format = F_RAW;
                }
                memset(&c->z, 0, sizeof c->z);
                if (inflateInit2(&c->z, bits_of(c->format)) != Z_OK) {
                        return fail(c, "inflateInit2 failed");
                }
                c->open = true;
        }

        if (!c->open) {
                return fail(c, "data after end of stream");
        }

        usize off = 0;

        while (off < len) {
                if (c->end) {
                        if (c->coding == F_RAW) {
                                break;
                        }
                        if (c->coding != F_GZIP && c->coding != F_AUTO) {
                                return fail(c, "data after end of stream");
                        }
                        if (in[off] != 0x1F) {
                                break;
                        }
                        inflateReset(&c->z);
                        c->end = false;
                }

                c->z.next_in  = (u8 *)in + off;
                c->z.avail_in = len - off;

                for (;;) {
                        c->z.next_out  = room(ty, c, out, CHUNK);
                        c->z.avail_out = CHUNK;

                        int rc = inflate(&c->z, Z_NO_FLUSH);

                        if (rc != Z_OK && rc != Z_STREAM_END && rc != Z_BUF_ERROR) {
                                return fail(c, "invalid compressed data (%d)", rc);
                        }

                        usize n = CHUNK - c->z.avail_out;

                        if (grew(c, out, n, limit)) {
                                codec_close(c);
                                return RUN_TOO_BIG;
                        }

                        if (rc == Z_STREAM_END) {
                                c->end = true;
                                break;
                        }
                        if (c->z.avail_in == 0 && c->z.avail_out != 0) {
                                break;
                        }
                        if (rc == Z_BUF_ERROR && n == 0) {
                                break;
                        }
                }

                off = len - c->z.avail_in;
        }

        return RUN_OK;
}

static int
deflate_run(Ty *ty, Codec *c, u8 const *in, usize len, int op, CodecBytes *out)
{
        int mode = (op == OP_FINISH) ? Z_FINISH
                 : (op == OP_FLUSH)  ? Z_SYNC_FLUSH
                 :                     Z_NO_FLUSH;

        c->z.next_in  = (u8 *)in;
        c->z.avail_in = len;

        for (;;) {
                c->z.next_out  = room(ty, c, out, CHUNK);
                c->z.avail_out = CHUNK;

                int rc = deflate(&c->z, mode);

                if (rc != Z_OK && rc != Z_STREAM_END && rc != Z_BUF_ERROR) {
                        return fail(c, "deflate failed (%d)", rc);
                }

                grew(c, out, CHUNK - c->z.avail_out, -1);

                if (
                        (rc == Z_STREAM_END)
                     || (c->z.avail_out != 0 && c->z.avail_in == 0 && mode != Z_FINISH)
                ) {
                        break;
                }
        }

        return RUN_OK;
}

static int
brdec_run(Ty *ty, Codec *c, u8 const *in, usize len, CodecBytes *out, i64 limit)
{
        if (len == 0) {
                return RUN_OK;
        }

        c->any = true;

        if (!c->open || c->end) {
                return fail(c, "data after end of stream");
        }

        size_t ain = len;

        for (;;) {
                size_t aout = CHUNK;
                u8 *nout = room(ty, c, out, CHUNK);

                int rc = BrDec.BrotliDecoderDecompressStream(c->br, &ain, &in, &aout, &nout, NULL);

                if (grew(c, out, CHUNK - aout, limit)) {
                        codec_close(c);
                        return RUN_TOO_BIG;
                }

                switch (rc) {
                case BROTLI_SUCCESS:
                        c->end = true;
                        if (ain != 0) {
                                return fail(c, "data after end of stream");
                        }
                        return RUN_OK;

                case BROTLI_NEEDS_MORE_OUTPUT:
                        continue;

                case BROTLI_NEEDS_MORE_INPUT:
                        return RUN_OK;

                default:
                        return fail(
                                c,
                                "invalid compressed data (%s)",
                                BrDec.BrotliDecoderErrorString(BrDec.BrotliDecoderGetErrorCode(c->br))
                        );
                }
        }
}

static int
brenc_run(Ty *ty, Codec *c, u8 const *in, usize len, int op, CodecBytes *out)
{
        size_t ain = len;

        for (;;) {
                size_t aout = CHUNK;
                u8 *nout = room(ty, c, out, CHUNK);

                if (!BrEnc.BrotliEncoderCompressStream(c->br, op, &ain, &in, &aout, &nout, NULL)) {
                        return fail(c, "BrotliEncoderCompressStream failed");
                }

                grew(c, out, CHUNK - aout, -1);

                if (ain == 0 && !BrEnc.BrotliEncoderHasMoreOutput(c->br)) {
                        return RUN_OK;
                }
        }
}

static int
zdec_run(Ty *ty, Codec *c, u8 const *in, usize len, CodecBytes *out, i64 limit)
{
        if (len == 0) {
                return RUN_OK;
        }

        if (!c->open) {
                return fail(c, "decoder is closed");
        }

        ZSTD_inBuffer zin = { .src = in, .size = len };

        for (;;) {
                ZSTD_outBuffer zout = { .dst = room(ty, c, out, CHUNK), .size = CHUNK };

                size_t rc = ZSTD_decompressStream(c->zd, &zout, &zin);

                if (ZSTD_isError(rc)) {
                        return fail(c, "invalid compressed data (%s)", ZSTD_getErrorName(rc));
                }

                c->left = rc;

                if (grew(c, out, zout.pos, limit)) {
                        codec_close(c);
                        return RUN_TOO_BIG;
                }

                if (zin.pos == zin.size && zout.pos < CHUNK) {
                        return RUN_OK;
                }
        }
}

static int
zenc_run(Ty *ty, Codec *c, u8 const *in, usize len, int op, CodecBytes *out)
{
        ZSTD_inBuffer zin = { .src = in, .size = len };
        ZSTD_EndDirective end = (op == OP_FINISH) ? ZSTD_e_end
                              : (op == OP_FLUSH)  ? ZSTD_e_flush
                              :                     ZSTD_e_continue;

        for (;;) {
                ZSTD_outBuffer zout = { .dst = room(ty, c, out, CHUNK), .size = CHUNK };

                size_t rc = ZSTD_compressStream2(c->zc, &zout, &zin, end);

                if (ZSTD_isError(rc)) {
                        return fail(c, "%s", ZSTD_getErrorName(rc));
                }

                grew(c, out, zout.pos, -1);

                if (
                        (end == ZSTD_e_continue && zin.pos == zin.size)
                     || (end != ZSTD_e_continue && rc == 0)
                ) {
                        return RUN_OK;
                }
        }
}

static Value
autoptr(Ty *ty, void *p, void (*dtor)(void *))
{
        Value *d = mAo(sizeof (Value [2]), GC_FFI_AUTO);

        d[0] = PTR((void *)dtor);
        d[1] = PTR(p);

        return GCPTR(p, d);
}

static Codec *
codec_arg(Ty *ty, char const *ctx, Value v)
{
        if (v.type != VALUE_PTR || v.ptr == NULL) {
                TyBuiltinBadArg(ty, ctx, "z", "Ptr", &v);
        }

        return v.ptr;
}

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

        case VALUE_NIL:
                *p = (u8 const *)"";
                *n = 0;
                break;

        default:
                TyBuiltinBadArg(ty, ctx, name, "String | Blob", &v);
        }
}

static Blob *
new_blob(Ty *ty)
{
        return value_blob_new(ty);
}

// _codec.has?(lib: String) -> Bool
TY_BUILTIN(codec_has)
{
        brotli();

        char const *s = (char const *)ss(lib);
        usize n = sN(lib);

#define IS(w) (n == sizeof (w) - 1 && memcmp(s, (w), n) == 0)
        return BOOLEAN(
                IS("brotlidec") ? HaveBrDec
              : IS("brotlienc") ? HaveBrEnc
              : IS("zlib")      ? true
              : IS("zstd")      ? true
              :                   false
        );
#undef IS
}

static char const *
codec_init(Codec *c, int level)
{
        c->coding = c->format;
        c->open   = (c->kind != K_INFLATE);

        switch (c->kind) {
        case K_INFLATE:
                break;

        case K_DEFLATE:
                if (deflateInit2(&c->z, level, Z_DEFLATED, bits_of(c->format), 8, Z_DEFAULT_STRATEGY) != Z_OK) {
                        return "deflateInit2 failed";
                }
                break;

        case K_BR_DEC:
                brotli();
                if (!HaveBrDec) {
                        return "libbrotlidec is not installed";
                }
                if ((c->br = BrDec.BrotliDecoderCreateInstance(NULL, NULL, NULL)) == NULL) {
                        return "BrotliDecoderCreateInstance failed";
                }
                break;

        case K_BR_ENC:
                brotli();
                if (!HaveBrEnc) {
                        return "libbrotlienc is not installed";
                }
                if ((c->br = BrEnc.BrotliEncoderCreateInstance(NULL, NULL, NULL)) == NULL) {
                        return "BrotliEncoderCreateInstance failed";
                }
                BrEnc.BrotliEncoderSetParameter(c->br, BROTLI_PARAM_QUALITY, max(0, min(level, 11)));
                BrEnc.BrotliEncoderSetParameter(c->br, BROTLI_PARAM_LGWIN,   22);
                break;

        case K_ZSTD_DEC:
                if ((c->zd = ZSTD_createDCtx()) == NULL) {
                        return "ZSTD_createDCtx failed";
                }
                ZSTD_DCtx_setParameter(c->zd, ZSTD_d_windowLogMax, 27);
                break;

        case K_ZSTD_ENC:
                if ((c->zc = ZSTD_createCCtx()) == NULL) {
                        return "ZSTD_createCCtx failed";
                }
                ZSTD_CCtx_setParameter(c->zc, ZSTD_c_compressionLevel, level);
                break;
        }

        return NULL;
}

Codec *
CodecNew(char const *s, usize n, bool encode, int level, char const **err)
{
        Codec c = { .first = true };

#define IS(w) (n == sizeof (w) - 1 && memcmp(s, (w), n) == 0)
        if (IS("gzip") || IS("x-gzip")) {
                c.format = F_GZIP;
                c.kind   = encode ? K_DEFLATE : K_INFLATE;
        } else if (IS("deflate")) {
                c.format = F_ZLIB;
                c.kind   = encode ? K_DEFLATE : K_INFLATE;
        } else if (IS("raw-deflate")) {
                c.format = F_RAW;
                c.kind   = encode ? K_DEFLATE : K_INFLATE;
        } else if (IS("zlib-auto")) {
                c.format = F_AUTO;
                c.kind   = K_INFLATE;
        } else if (IS("br")) {
                c.kind = encode ? K_BR_ENC : K_BR_DEC;
        } else if (IS("zstd")) {
                c.kind = encode ? K_ZSTD_ENC : K_ZSTD_DEC;
        } else {
                *err = "unsupported content coding";
                return NULL;
        }
#undef IS

        Codec *p = xmA(sizeof *p);
        *p = c;

        if ((*err = codec_init(p, level)) != NULL) {
                xmF(p);
                return NULL;
        }

        return p;
}

int
CodecRun(Ty *ty, Codec *c, void const *data, usize len, int op, CodecBytes *out, bool gc, i64 limit)
{
        u8 const *in = data;

        c->gc = gc;

        switch (c->kind) {
        case K_INFLATE:  return inflate_run(ty, c, in, len, out, limit);
        case K_BR_DEC:   return brdec_run(ty, c, in, len, out, limit);
        case K_ZSTD_DEC: return zdec_run(ty, c, in, len, out, limit);
        }

        if (!c->open) {
                return fail(c, "encoder is closed");
        }

        return (c->kind == K_DEFLATE) ? deflate_run(ty, c, in, len, op, out)
             : (c->kind == K_BR_ENC)  ? brenc_run(ty, c, in, len, op, out)
             :                          zenc_run(ty, c, in, len, op, out);
}

bool
CodecDone(Codec *c)
{
        return (c->kind == K_INFLATE)  ? (c->end || c->first)
             : (c->kind == K_BR_DEC)   ? (c->end || !c->any)
             : (c->kind == K_ZSTD_DEC) ? (c->left == 0)
             :                           true;
}

void
CodecReset(Codec *c)
{
        c->total = 0;

        if (!c->open) {
                return;
        }

        switch (c->kind) {
        case K_INFLATE:  c->end = false; inflateReset(&c->z);                          break;
        case K_DEFLATE:  deflateReset(&c->z);                                          break;
        case K_ZSTD_DEC: c->left = 0; ZSTD_DCtx_reset(c->zd, ZSTD_reset_session_only); break;
        case K_ZSTD_ENC: ZSTD_CCtx_reset(c->zc, ZSTD_reset_session_only);              break;
        }
}

void
CodecFree(Codec *c)
{
        if (c != NULL) {
                codec_free(c);
        }
}

char const *
CodecError(Codec const *c)
{
        return c->msg;
}

bool
CodecHave(char const *lib)
{
        brotli();

        return (strcmp(lib, "brotlidec") == 0) ? HaveBrDec
             : (strcmp(lib, "brotlienc") == 0) ? HaveBrEnc
             :                                   true;
}

// _codec.open(coding: String, encode: Bool, level: Int = 0) -> Ptr | String
TY_BUILTIN(codec_open)
{
        char const *err;
        Codec *c = CodecNew((char const *)ss(coding), sN(coding), encode, level, &err);

        return (c == NULL) ? vSsz(err) : autoptr(ty, c, codec_free);
}

// _codec.run(z: Ptr, data: String | Blob | nil, out: Blob, op: Int = 0, limit: Int = -1) -> Int
TY_BUILTIN(codec_run)
{
        Codec *c = codec_arg(ty, _name__, z);
        u8 const *in;
        usize len;

        bytes_arg(ty, _name__, "data", data, &in, &len);

        return INTEGER(CodecRun(ty, c, in, len, op, (CodecBytes *)out, true, limit));
}

// _codec.finish(z: Ptr) -> Bool
TY_BUILTIN(codec_finish)
{
        Codec *c = codec_arg(ty, _name__, z);
        bool ok = CodecDone(c);

        codec_close(c);

        return BOOLEAN(ok);
}

// _codec.reset(z: Ptr) -> nil
TY_BUILTIN(codec_reset)
{
        CodecReset(codec_arg(ty, _name__, z));
        return NIL;
}

// _codec.close(z: Ptr) -> nil
TY_BUILTIN(codec_close)
{
        codec_close(codec_arg(ty, _name__, z));
        return NIL;
}

// _codec.message(z: Ptr) -> String
TY_BUILTIN(codec_message)
{
        return vSsz(codec_arg(ty, _name__, z)->msg);
}

// _codec.zlib-version() -> String
TY_BUILTIN(codec_zlib_version)
{
        return vSsz(zlibVersion());
}

// _codec.zstd-version() -> String
TY_BUILTIN(codec_zstd_version)
{
        return vSsz(ZSTD_versionString());
}

// _codec.crc32(data: String | Blob, crc: Int = 0) -> Int
TY_BUILTIN(codec_crc32)
{
        u8 const *p;
        usize n;

        bytes_arg(ty, _name__, "data", data, &p, &n);

        return INTEGER(crc32_z(crc, p, n));
}

// _codec.adler32(data: String | Blob, adler: Int = 1) -> Int
TY_BUILTIN(codec_adler32)
{
        u8 const *p;
        usize n;

        bytes_arg(ty, _name__, "data", data, &p, &n);

        return INTEGER(adler32_z(adler, p, n));
}

// _codec.zlib-compress(data: String | Blob, level: Int = -1) -> Blob
TY_BUILTIN(codec_zlib_compress)
{
        u8 const *p;
        usize n;

        bytes_arg(ty, _name__, "data", data, &p, &n);

        uLongf size = compressBound(n);
        Blob *out = new_blob(ty);
        Value result = BLOB(out);

        gP(&result);
        vvR(*out, size);
        int rc = compress2(vv(*out), &size, p, n, level);
        gX();

        if (rc != Z_OK) {
                bP("%s", zError(rc));
        }

        vN(*out) = size;

        return result;
}

// _codec.zstd-compress(data: String | Blob, level: Int = 3) -> Blob
TY_BUILTIN(codec_zstd_compress)
{
        u8 const *p;
        usize n;

        bytes_arg(ty, _name__, "data", data, &p, &n);

        usize bound = ZSTD_compressBound(n);
        Blob *out = new_blob(ty);
        Value result = BLOB(out);

        gP(&result);
        vvR(*out, bound);
        usize size = ZSTD_compress(vv(*out), bound, p, n, level);
        gX();

        if (ZSTD_isError(size)) {
                bP("%s", ZSTD_getErrorName(size));
        }

        vN(*out) = size;

        return result;
}

// _codec.zstd-content-size(data: String | Blob) -> Int
TY_BUILTIN(codec_zstd_content_size)
{
        u8 const *p;
        usize n;

        bytes_arg(ty, _name__, "data", data, &p, &n);

        return INTEGER((i64)ZSTD_getFrameContentSize(p, n));
}

// _codec.zstd-decompress(data: String | Blob, size: Int) -> Blob
TY_BUILTIN(codec_zstd_decompress)
{
        u8 const *p;
        usize n;

        bytes_arg(ty, _name__, "data", data, &p, &n);

        if (size < 0) {
                bP("negative size: %"PRIi64, size);
        }

        Blob *out = new_blob(ty);
        Value result = BLOB(out);

        gP(&result);
        vvR(*out, max(size, 1));
        usize got = ZSTD_decompress(vv(*out), size, p, n);
        gX();

        if (ZSTD_isError(got)) {
                bP("%s", ZSTD_getErrorName(got));
        }

        vN(*out) = got;

        return result;
}

/* vim: set sts=8 sw=8 expandtab: */
