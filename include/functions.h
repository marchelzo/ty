#ifndef FUNCTIONS_H_INCLUDED
#define FUNCTIONS_H_INCLUDED

#include "value.h"

struct value
builtin_print(value_vector *args);

struct value
builtin_die(value_vector *args);

struct value
builtin_rand(value_vector *args);

struct value
builtin_abs(value_vector *args);

struct value
builtin_hash(value_vector *args);

struct value
builtin_int(value_vector *args);

struct value
builtin_float(value_vector *args);

struct value
builtin_str(value_vector *args);

struct value
builtin_bool(value_vector *args);

struct value
builtin_regex(value_vector *args);

struct value
builtin_blob(value_vector *args);

struct value
builtin_max(value_vector *args);

struct value
builtin_min(value_vector *args);

struct value
builtin_read(value_vector *args);

struct value
builtin_log2(value_vector *args);

struct value
builtin_pow(value_vector *args);

struct value
builtin_cbrt(value_vector *args);

struct value
builtin_sqrt(value_vector *args);

struct value
builtin_exp(value_vector *args);

struct value
builtin_log(value_vector *args);

struct value
builtin_atan2(value_vector *args);

struct value
builtin_atan(value_vector *args);

struct value
builtin_asin(value_vector *args);

struct value
builtin_acos(value_vector *args);

struct value
builtin_tan(value_vector *args);

struct value
builtin_sin(value_vector *args);

struct value
builtin_cos(value_vector *args);

struct value
builtin_bit_and(value_vector *args);

struct value
builtin_bit_or(value_vector *args);

struct value
builtin_bit_xor(value_vector *args);

struct value
builtin_bit_shift_left(value_vector *args);

struct value
builtin_bit_shift_right(value_vector *args);

struct value
builtin_bit_complement(value_vector *args);

struct value
builtin_getenv(value_vector *args);

struct value
builtin_setenv(value_vector *args);

struct value
builtin_json_parse(value_vector *args);

struct value
builtin_json_encode(value_vector *args);

struct value
builtin_os_open(value_vector *args);

struct value
builtin_os_close(value_vector *args);

struct value
builtin_os_read(value_vector *args);

struct value
builtin_os_write(value_vector *args);

struct value
builtin_os_listdir(value_vector *args);

struct value
builtin_os_usleep(value_vector *args);

struct value
builtin_os_fcntl(value_vector *args);

struct value
builtin_os_spawn(value_vector *args);

struct value
builtin_os_stat(value_vector *args);

struct value
builtin_os_fork(value_vector *args);

struct value
builtin_os_pipe(value_vector *args);

struct value
builtin_os_dup2(value_vector *args);

struct value
builtin_os_poll(value_vector *args);

struct value
builtin_os_getaddrinfo(value_vector *args);

struct value
builtin_os_bind(value_vector *args);

struct value
builtin_os_socket(value_vector *args);

struct value
builtin_os_listen(value_vector *args);

struct value
builtin_os_accept(value_vector *args);

struct value
builtin_os_connect(value_vector *args);

struct value
builtin_os_shutdown(value_vector *args);

struct value
builtin_os_waitpid(value_vector *args);

struct value
builtin_os_WIFEXITED(value_vector *args);

struct value
builtin_os_WIFSIGNALED(value_vector *args);

#ifdef WIFCONTINUED
struct value
builtin_os_WIFCONTINUED(value_vector *args);
#endif

struct value
builtin_os_WIFSTOPPED(value_vector *args);

#ifdef WCOREDUMP
struct value
builtin_os_WCOREDUMP(value_vector *args);
#endif

struct value
builtin_os_WEXITSTATUS(value_vector *args);

struct value
builtin_os_WTERMSIG(value_vector *args);

struct value
builtin_os_WSTOPSIG(value_vector *args);

struct value
builtin_os_getpid(value_vector *args);

struct value
builtin_os_getppid(value_vector *args);

struct value
builtin_os_getuid(value_vector *args);

struct value
builtin_os_geteuid(value_vector *args);

struct value
builtin_os_getgid(value_vector *args);

struct value
builtin_os_getegid(value_vector *args);

struct value
builtin_os_setuid(value_vector *args);

struct value
builtin_os_seteuid(value_vector *args);

struct value
builtin_os_setgid(value_vector *args);

struct value
builtin_os_setegid(value_vector *args);

struct value
builtin_os_kill(value_vector *args);

struct value
builtin_os_exit(value_vector *args);

struct value
builtin_os_utime(value_vector *args);

struct value
builtin_os_exec(value_vector *args);

struct value
builtin_errno_get(value_vector *args);

struct value
builtin_errno_str(value_vector *args);

struct value
builtin_time_time(value_vector *args);

#endif
