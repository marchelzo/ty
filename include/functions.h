#ifndef FUNCTIONS_H_INCLUDED
#define FUNCTIONS_H_INCLUDED

#include "value.h"

struct value
builtin_print(int argc);

struct value
builtin_slurp(int argc);

struct value
builtin_die(int argc);

struct value
builtin_rand(int argc);

struct value
builtin_abs(int argc);

struct value
builtin_round(int argc);

struct value
builtin_ceil(int argc);

struct value
builtin_gcd(int argc);

struct value
builtin_lcm(int argc);

struct value
builtin_hash(int argc);

struct value
builtin_int(int argc);

struct value
builtin_float(int argc);

struct value
builtin_str(int argc);

struct value
builtin_bool(int argc);

struct value
builtin_regex(int argc);

struct value
builtin_blob(int argc);

struct value
builtin_max(int argc);

struct value
builtin_min(int argc);

struct value
builtin_read(int argc);

struct value
builtin_log2(int argc);

struct value
builtin_pow(int argc);

struct value
builtin_cbrt(int argc);

struct value
builtin_sqrt(int argc);

struct value
builtin_exp(int argc);

struct value
builtin_log(int argc);

struct value
builtin_atan2(int argc);

struct value
builtin_atan(int argc);

struct value
builtin_asin(int argc);

struct value
builtin_acos(int argc);

struct value
builtin_tan(int argc);

struct value
builtin_sin(int argc);

struct value
builtin_cos(int argc);

struct value
builtin_bit_and(int argc);

struct value
builtin_bit_or(int argc);

struct value
builtin_bit_xor(int argc);

struct value
builtin_bit_shift_left(int argc);

struct value
builtin_bit_shift_right(int argc);

struct value
builtin_bit_complement(int argc);

struct value
builtin_getenv(int argc);

struct value
builtin_setenv(int argc);

struct value
builtin_json_parse(int argc);

struct value
builtin_json_encode(int argc);

struct value
builtin_md5(int argc);

struct value
builtin_os_open(int argc);

struct value
builtin_os_close(int argc);

struct value
builtin_os_read(int argc);

struct value
builtin_os_write(int argc);

struct value
builtin_os_listdir(int argc);

struct value
builtin_os_usleep(int argc);

struct value
builtin_os_fcntl(int argc);

struct value
builtin_os_spawn(int argc);

struct value
builtin_os_stat(int argc);

struct value
builtin_os_fork(int argc);

struct value
builtin_os_pipe(int argc);

struct value
builtin_os_dup2(int argc);

struct value
builtin_os_poll(int argc);

struct value
builtin_os_getaddrinfo(int argc);

struct value
builtin_os_bind(int argc);

struct value
builtin_os_socket(int argc);

struct value
builtin_os_listen(int argc);

struct value
builtin_os_accept(int argc);

struct value
builtin_os_connect(int argc);

struct value
builtin_os_shutdown(int argc);

struct value
builtin_os_waitpid(int argc);

struct value
builtin_os_WIFEXITED(int argc);

struct value
builtin_os_WIFSIGNALED(int argc);

#ifdef WIFCONTINUED
struct value
builtin_os_WIFCONTINUED(int argc);
#endif

struct value
builtin_os_WIFSTOPPED(int argc);

#ifdef WCOREDUMP
struct value
builtin_os_WCOREDUMP(int argc);
#endif

struct value
builtin_os_WEXITSTATUS(int argc);

struct value
builtin_os_WTERMSIG(int argc);

struct value
builtin_os_WSTOPSIG(int argc);

struct value
builtin_os_getpid(int argc);

struct value
builtin_os_getppid(int argc);

struct value
builtin_os_getuid(int argc);

struct value
builtin_os_geteuid(int argc);

struct value
builtin_os_getgid(int argc);

struct value
builtin_os_getegid(int argc);

struct value
builtin_os_setuid(int argc);

struct value
builtin_os_seteuid(int argc);

struct value
builtin_os_setgid(int argc);

struct value
builtin_os_setegid(int argc);

struct value
builtin_os_kill(int argc);

struct value
builtin_os_exit(int argc);

struct value
builtin_os_utime(int argc);

struct value
builtin_os_exec(int argc);

struct value
builtin_errno_get(int argc);

struct value
builtin_errno_str(int argc);

struct value
builtin_time_time(int argc);

struct value
builtin_time_utime(int argc);

struct value
builtin_time_localtime(int argc);

struct value
builtin_time_strftime(int argc);

struct value
builtin_time_strptime(int argc);

#endif
