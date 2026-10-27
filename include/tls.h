#ifndef TLS_H_INCLUDED
#define TLS_H_INCLUDED

#include "ty.h"

typedef struct tls Tls;

bool
TlsLoad(char const **why);

Tls *
TlsNew(void *ctx, bool server, char const *host);

void
TlsFree(Tls *t);

int
TlsHandshake(Ty *ty, Tls *t, Value const *ctx);

bool
TlsDone(Tls const *t);

bool
TlsFeed(Tls *t, void const *p, usize n);

void
TlsFeedEof(Tls *t);

isize
TlsRead(Tls *t, void *p, usize n);

isize
TlsWrite(Tls *t, void const *p, usize n);

usize
TlsPending(Tls const *t);

usize
TlsBuffered(Tls const *t);

isize
TlsDrain(Tls *t, void *p, usize n);

void
TlsShutdown(Tls *t);

bool
TlsEof(Tls const *t);

bool
TlsAlpn(Tls const *t, char const **p, unsigned *n);

long
TlsVerifyResult(Tls const *t);

char const *
TlsVerifyError(long r);

void
TlsErrors(char *buf, usize n);

#endif

/* vim: set sts=8 sw=8 expandtab: */
