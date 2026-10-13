#!/bin/sh

echo '#include <sys/syscall.h>' \
    | cc -dM -E - \
    | grep -E '#define SYS_[a-z0-9_]+\s' \
    | cut -d' ' -f2 \
    | sort \
    | uniq \
	| awk '{printf("{ .name = \"%s\", .nr = %s },\n", substr($1, 5), $1)}'
