#ifndef TEST_H_INCLUDED
#define TEST_H_INCLUDED

#include <stdbool.h>
#include <stdio.h>

#define MACRO_CONCAT(A, B) MACRO_CONCAT_(A, B)
#define MACRO_CONCAT_(A, B) A##B
#define TEST(name) void MACRO_CONCAT(TEST_, MACRO_CONCAT(FILENAME, MACRO_CONCAT(_, name))) (bool *test_status_bool)

#define claim(b) \
        if (!(b)) { \
                printf( \
                        "\x1b[31;1mfailed\n\x1b[37;1m    assertion failed\x1b[0m: %s:%d (\x1b[33;1m%s\x1b[0m)\n", \
                        __FILE__, \
                        __LINE__, \
                        #b \
                ); \
                *test_status_bool = false; \
                return; \
        }

#endif
