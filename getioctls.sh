echo '#include <sys/ioctl.h>' \
    | gcc -dM -E - \
    | grep '#define [A-Z]\+IOC' \
    | cut -d' ' -f2 \
	| grep -v ISO7816 \
    | sort \
    | uniq \
	| awk '{printf("{ .module = \"ioctls\", .name = \"%s\", .value = INT(%s) },\n", $1, $1)}' \
    > include/ioctl_constants.h
