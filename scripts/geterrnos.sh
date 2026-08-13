#!/bin/sh

echo '#include <errno.h>' \
    | cc -dM -E - \
    | grep -E '#define E[A-Z]+\s' \
    | cut -d' ' -f2 \
    | sort \
    | uniq \
	| awk '{printf("{ .module = \"errno\", .name = \"%s\", .init = INT(%s) },\n", $1, $1)}'
