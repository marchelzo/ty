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
builtin_iround(int argc);

struct value
builtin_ceil(int argc);

struct value
builtin_floor(int argc);

struct value
builtin_gcd(int argc);

struct value
builtin_lcm(int argc);

struct value
builtin_hash(int argc);

struct value
builtin_object(int argc);

struct value
builtin_bind(int argc);

struct value
builtin_apply(int argc);

struct value
builtin_type(int argc);

struct value
builtin_subclass(int argc);

struct value
builtin_members(int argc);

struct value
builtin_member(int argc);

struct value
builtin_int(int argc);

struct value
builtin_float(int argc);

struct value
builtin_isnan(int argc);

struct value
builtin_str(int argc);

struct value
builtin_bool(int argc);

struct value
builtin_regex(int argc);

struct value
builtin_array(int argc);

struct value
builtin_dict(int argc);

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
builtin_ord(int argc);

struct value
builtin_chr(int argc);

struct value
builtin_os_open(int argc);

struct value
builtin_os_umask(int argc);

struct value
builtin_os_close(int argc);

struct value
builtin_os_mktemp(int argc);

struct value
builtin_os_opendir(int argc);

struct value
builtin_os_readdir(int argc);

struct value
builtin_os_telldir(int argc);

struct value
builtin_os_seekdir(int argc);

struct value
builtin_os_rewinddir(int argc);

struct value
builtin_os_closedir(int argc);

struct value
builtin_os_getcwd(int argc);

struct value
builtin_os_chdir(int argc);

struct value
builtin_os_unlink(int argc);

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
builtin_os_thread(int argc);

struct value
builtin_os_join(int argc);

struct value
builtin_os_pipe(int argc);

struct value
builtin_os_dup2(int argc);

struct value
builtin_os_poll(int argc);

struct value
builtin_os_epoll_create(int argc);

struct value
builtin_os_epoll_ctl(int argc);

struct value
builtin_os_epoll_wait(int argc);

struct value
builtin_os_getaddrinfo(int argc);

struct value
builtin_os_bind(int argc);

struct value
builtin_os_socket(int argc);

struct value
builtin_os_setsockopt(int argc);

struct value
builtin_os_getsockopt(int argc);

struct value
builtin_os_listen(int argc);

struct value
builtin_os_accept(int argc);

struct value
builtin_os_connect(int argc);

struct value
builtin_os_recvfrom(int argc);

struct value
builtin_os_sendto(int argc);

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
builtin_os_signal(int argc);

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

struct value
builtin_stdio_fdopen(int argc);

struct value
builtin_stdio_fgets(int argc);

struct value
builtin_stdio_fread(int argc);

struct value
builtin_stdio_read_signed(int argc);

struct value
builtin_stdio_read_unsigned(int argc);

struct value
builtin_stdio_read_float(int argc);

struct value
builtin_stdio_read_double(int argc);

struct value
builtin_stdio_puts(int argc);

struct value
builtin_stdio_fwrite(int argc);

struct value
builtin_stdio_fgetc(int argc);

struct value
builtin_stdio_slurp(int argc);

struct value
builtin_stdio_fflush(int argc);

struct value
builtin_stdio_fclose(int argc);

struct value
builtin_stdio_clearerr(int argc);

struct value
builtin_stdio_fseek(int argc);

struct value
builtin_stdio_ftell(int argc);

struct value
builtin_stdio_setvbuf(int argc);

#endif
