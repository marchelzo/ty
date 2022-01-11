echo '#include <sys/ioctl.h>' > ioctl_list.c
echo '#include <stdio.h>' >> ioctl_list.c
echo 'int main(void) {' >> ioctl_list.c


echo '#include <sys/ioctl.h>' \
    | gcc -dM -E - \
    | grep '#define [A-Z]\+IOC' \
    | cut -d' ' -f2 \
	| grep -v ISO7816 \
    | sort \
    | uniq \
	| awk '{printf("printf(\"{ .module = \\\"ioctl\\\", .name = \\\"%%s\\\", .value = INT(%%lu) },\\n\", \"%s\", (unsigned long)%s);\n", $1, $1)}' \
    >> ioctl_list.c;

echo 'return 0;' >> ioctl_list.c
echo '}' >> ioctl_list.c
