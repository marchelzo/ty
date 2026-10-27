#ifndef CODEC_H_INCLUDED
#define CODEC_H_INCLUDED

#include "ty.h"

typedef struct codec Codec;
typedef vec(u8) CodecBytes;

enum {
        CODEC_PROCESS,
        CODEC_FLUSH,
        CODEC_FINISH
};

enum {
        CODEC_OK      =  0,
        CODEC_ERROR   = -1,
        CODEC_TOO_BIG = -2
};

Codec *
CodecNew(char const *coding, usize n, bool encode, int level, char const **err);

int
CodecRun(Ty *ty, Codec *c, void const *in, usize len, int op, CodecBytes *out, bool gc, i64 limit);

bool
CodecDone(Codec *c);

void
CodecReset(Codec *c);

void
CodecFree(Codec *c);

char const *
CodecError(Codec const *c);

bool
CodecHave(char const *lib);

#endif

/* vim: set sts=8 sw=8 expandtab: */
