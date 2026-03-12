#!/bin/sh

echo '#include <sys/ioctl.h>' \
    | cc -dM -E - \
    | grep '#define [A-Z]\+IOC' \
    | cut -d' ' -f2 \
	| grep -v ISO7816 \
	| grep -v '[^a-zA-Z0-9]' \
    | sort \
    | uniq \
	| awk '{printf("{ .module = \"ioctls\", .name = \"%s\", .value = INT(%s) },\n", $1, $1)}'
