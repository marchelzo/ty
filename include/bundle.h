#ifndef BUNDLE_H_INCLUDED
#define BUNDLE_H_INCLUDED

#include "ty.h"

#define TY_BUNDLE_MAGIC "TYBNDL01"

enum {
        TY_BUNDLE_RUN = 1 << 0,
};

typedef struct {
        char magic[8];
        u64  offset;
        u64  size;
        u64  hash;
        u64  flags;
        u64  reserved;
} BundleTrailer;

typedef struct {
        u32 len;
        u32 mode;
        u64 size;
} BundleEntry;

typedef enum {
        BUNDLE_NONE,
        BUNDLE_READY,
        BUNDLE_BROKEN,
} BundleState;

bool
bundle_locate(int fd, BundleTrailer *out);

bool
bundle_put_file(char const *dir, char const *rel, void const *data, usize n, u32 mode);

BundleState
bundle_state(void);

char const *
bundle_dir(void);

char const *
bundle_entry(void);

char const *
bundle_error(void);

int
bundle_flags(char const *const **out);

char const *
bundle_native(char const *path);

void
bundle_preload(void);

void
bundle_snapshot(void);

int
bundle_create(Ty *ty, char const *script, char const *out, char **flags, int nflags);

#endif
