#ifndef FUNCTIONS_H_INCLUDED
#define FUNCTIONS_H_INCLUDED

#include "value.h"

struct value
builtin_print(int argc, struct value *kwargs);

struct value
builtin_doc(int argc, struct value *kwargs);

struct value
builtin_eprint(int argc, struct value *kwargs);

struct value
builtin_slurp(int argc, struct value *kwargs);

struct value
builtin_die(int argc, struct value *kwargs);

struct value
builtin_rand(int argc, struct value *kwargs);

struct value
builtin_abs(int argc, struct value *kwargs);

struct value
builtin_round(int argc, struct value *kwargs);

struct value
builtin_iround(int argc, struct value *kwargs);

struct value
builtin_ceil(int argc, struct value *kwargs);

struct value
builtin_floor(int argc, struct value *kwargs);

struct value
builtin_gcd(int argc, struct value *kwargs);

struct value
builtin_lcm(int argc, struct value *kwargs);

struct value
builtin_hash(int argc, struct value *kwargs);

struct value
builtin_object(int argc, struct value *kwargs);

struct value
builtin_bind(int argc, struct value *kwargs);

struct value
builtin_apply(int argc, struct value *kwargs);

struct value
builtin_type(int argc, struct value *kwargs);

struct value
builtin_subclass(int argc, struct value *kwargs);

struct value
builtin_members(int argc, struct value *kwargs);

struct value
builtin_member(int argc, struct value *kwargs);

struct value
builtin_finalizer(int argc, struct value *kwargs);

struct value
builtin_int(int argc, struct value *kwargs);

struct value
builtin_float(int argc, struct value *kwargs);

struct value
builtin_isnan(int argc, struct value *kwargs);

struct value
builtin_str(int argc, struct value *kwargs);

struct value
builtin_fmt(int argc, struct value *kwargs);

struct value
builtin_bool(int argc, struct value *kwargs);

struct value
builtin_regex(int argc, struct value *kwargs);

struct value
builtin_array(int argc, struct value *kwargs);

struct value
builtin_tuple(int argc, struct value *kwargs);

struct value
builtin_dict(int argc, struct value *kwargs);

struct value
builtin_blob(int argc, struct value *kwargs);

struct value
builtin_max(int argc, struct value *kwargs);

struct value
builtin_min(int argc, struct value *kwargs);

struct value
builtin_read(int argc, struct value *kwargs);

struct value
builtin_log2(int argc, struct value *kwargs);

struct value
builtin_log10(int argc, struct value *kwargs);

struct value
builtin_pow(int argc, struct value *kwargs);

struct value
builtin_cbrt(int argc, struct value *kwargs);

struct value
builtin_sqrt(int argc, struct value *kwargs);

struct value
builtin_exp(int argc, struct value *kwargs);

struct value
builtin_log(int argc, struct value *kwargs);

struct value
builtin_sinh(int argc, struct value *kwargs);

struct value
builtin_cosh(int argc, struct value *kwargs);

struct value
builtin_tanh(int argc, struct value *kwargs);

struct value
builtin_atan2(int argc, struct value *kwargs);

struct value
builtin_atan(int argc, struct value *kwargs);

struct value
builtin_asin(int argc, struct value *kwargs);

struct value
builtin_acos(int argc, struct value *kwargs);

struct value
builtin_tan(int argc, struct value *kwargs);

struct value
builtin_sin(int argc, struct value *kwargs);

struct value
builtin_cos(int argc, struct value *kwargs);

struct value
builtin_bit_and(int argc, struct value *kwargs);

struct value
builtin_bit_or(int argc, struct value *kwargs);

struct value
builtin_bit_xor(int argc, struct value *kwargs);

struct value
builtin_bit_shift_left(int argc, struct value *kwargs);

struct value
builtin_bit_shift_right(int argc, struct value *kwargs);

struct value
builtin_bit_complement(int argc, struct value *kwargs);

struct value
builtin_getenv(int argc, struct value *kwargs);

struct value
builtin_setenv(int argc, struct value *kwargs);

struct value
builtin_locale_setlocale(int argc, struct value *kwargs);

struct value
builtin_json_parse(int argc, struct value *kwargs);

struct value
builtin_json_encode(int argc, struct value *kwargs);

struct value
builtin_md5(int argc, struct value *kwargs);

struct value
builtin_sha1(int argc, struct value *kwargs);

struct value
builtin_sha256(int argc, struct value *kwargs);

struct value
builtin_base64_encode(int argc, struct value *kwargs);

struct value
builtin_base64_decode(int argc, struct value *kwargs);

struct value
builtin_ord(int argc, struct value *kwargs);

struct value
builtin_chr(int argc, struct value *kwargs);

struct value
builtin_os_open(int argc, struct value *kwargs);

struct value
builtin_os_umask(int argc, struct value *kwargs);

struct value
builtin_os_close(int argc, struct value *kwargs);

struct value
builtin_os_mktemp(int argc, struct value *kwargs);

struct value
builtin_os_opendir(int argc, struct value *kwargs);

struct value
builtin_os_readdir(int argc, struct value *kwargs);

struct value
builtin_os_telldir(int argc, struct value *kwargs);

struct value
builtin_os_seekdir(int argc, struct value *kwargs);

struct value
builtin_os_rewinddir(int argc, struct value *kwargs);

struct value
builtin_os_closedir(int argc, struct value *kwargs);

struct value
builtin_os_getcwd(int argc, struct value *kwargs);

struct value
builtin_os_chdir(int argc, struct value *kwargs);

struct value
builtin_os_mkdir(int argc, struct value *kwargs);

struct value
builtin_os_rmdir(int argc, struct value *kwargs);

struct value
builtin_os_unlink(int argc, struct value *kwargs);

struct value
builtin_os_rename(int argc, struct value *kwargs);

struct value
builtin_os_read(int argc, struct value *kwargs);

struct value
builtin_os_write(int argc, struct value *kwargs);

struct value
builtin_os_fsync(int argc, struct value *kwargs);

struct value
builtin_os_sync(int argc, struct value *kwargs);

struct value
builtin_os_listdir(int argc, struct value *kwargs);

struct value
builtin_os_usleep(int argc, struct value *kwargs);

struct value
builtin_os_sleep(int argc, struct value *kwargs);

struct value
builtin_os_fcntl(int argc, struct value *kwargs);

struct value
builtin_os_spawn(int argc, struct value *kwargs);

struct value
builtin_os_stat(int argc, struct value *kwargs);

struct value
builtin_os_truncate(int argc, struct value *kwargs);

struct value
builtin_os_ftruncate(int argc, struct value *kwargs);

struct value
builtin_os_realpath(int argc, struct value *kwargs);

struct value
builtin_os_fork(int argc, struct value *kwargs);

struct value
builtin_os_isatty(int argc, struct value *kwargs);

struct value
builtin_termios_tcgetattr(int argc, struct value *kwargs);

struct value
builtin_termios_tcsetattr(int argc, struct value *kwargs);

struct value
builtin_thread_create(int argc, struct value *kwargs);

struct value
builtin_thread_mutex(int argc, struct value *kwargs);

struct value
builtin_thread_mutex_destroy(int argc, struct value *kwargs);

struct value
builtin_thread_join(int argc, struct value *kwargs);

struct value
builtin_thread_detach(int argc, struct value *kwargs);

struct value
builtin_thread_kill(int argc, struct value *kwargs);

struct value
builtin_thread_lock(int argc, struct value *kwargs);

struct value
builtin_thread_unlock(int argc, struct value *kwargs);

struct value
builtin_thread_trylock(int argc, struct value *kwargs);

struct value
builtin_thread_cond(int argc, struct value *kwargs);

struct value
builtin_thread_cond_destroy(int argc, struct value *kwargs);

struct value
builtin_thread_cond_broadcast(int argc, struct value *kwargs);

struct value
builtin_thread_cond_signal(int argc, struct value *kwargs);

struct value
builtin_thread_cond_wait(int argc, struct value *kwargs);

struct value
builtin_thread_getname(int argc, struct value *kwargs);

struct value
builtin_thread_self(int argc, struct value *kwargs);

struct value
builtin_thread_id(int argc, struct value *kwargs);

struct value
builtin_thread_setname(int argc, struct value *kwargs);

struct value
builtin_thread_send(int argc, struct value *kwargs);

struct value
builtin_thread_recv(int argc, struct value *kwargs);

struct value
builtin_thread_channel(int argc, struct value *kwargs);

struct value
builtin_thread_close(int argc, struct value *kwargs);

struct value
builtin_os_pipe(int argc, struct value *kwargs);

struct value
builtin_os_dup(int argc, struct value *kwargs);

struct value
builtin_os_dup2(int argc, struct value *kwargs);

struct value
builtin_os_poll(int argc, struct value *kwargs);

struct value
builtin_os_epoll_create(int argc, struct value *kwargs);

struct value
builtin_os_epoll_ctl(int argc, struct value *kwargs);

struct value
builtin_os_epoll_wait(int argc, struct value *kwargs);

struct value
builtin_os_getaddrinfo(int argc, struct value *kwargs);

struct value
builtin_os_gai_strerror(int argc, struct value *kwargs);

struct value
builtin_os_bind(int argc, struct value *kwargs);

struct value
builtin_os_socket(int argc, struct value *kwargs);

struct value
builtin_os_setsockopt(int argc, struct value *kwargs);

struct value
builtin_os_getsockopt(int argc, struct value *kwargs);

struct value
builtin_os_getpeername(int argc, struct value *kwargs);

struct value
builtin_os_getsockname(int argc, struct value *kwargs);

struct value
builtin_os_getnameinfo(int argc, struct value *kwargs);

struct value
builtin_os_listen(int argc, struct value *kwargs);

struct value
builtin_os_accept(int argc, struct value *kwargs);

struct value
builtin_os_connect(int argc, struct value *kwargs);

struct value
builtin_os_recvfrom(int argc, struct value *kwargs);

struct value
builtin_os_sendto(int argc, struct value *kwargs);

struct value
builtin_os_shutdown(int argc, struct value *kwargs);

struct value
builtin_os_waitpid(int argc, struct value *kwargs);

struct value
builtin_os_WIFEXITED(int argc, struct value *kwargs);

struct value
builtin_os_WIFSIGNALED(int argc, struct value *kwargs);

#ifdef WIFCONTINUED
struct value
builtin_os_WIFCONTINUED(int argc, struct value *kwargs);
#endif

struct value
builtin_os_WIFSTOPPED(int argc, struct value *kwargs);

#ifdef WCOREDUMP
struct value
builtin_os_WCOREDUMP(int argc, struct value *kwargs);
#endif

struct value
builtin_os_WEXITSTATUS(int argc, struct value *kwargs);

struct value
builtin_os_WTERMSIG(int argc, struct value *kwargs);

struct value
builtin_os_WSTOPSIG(int argc, struct value *kwargs);

struct value
builtin_os_getpid(int argc, struct value *kwargs);

struct value
builtin_os_getppid(int argc, struct value *kwargs);

struct value
builtin_os_getuid(int argc, struct value *kwargs);

struct value
builtin_os_geteuid(int argc, struct value *kwargs);

struct value
builtin_os_getgid(int argc, struct value *kwargs);

struct value
builtin_os_getegid(int argc, struct value *kwargs);

struct value
builtin_os_setuid(int argc, struct value *kwargs);

struct value
builtin_os_seteuid(int argc, struct value *kwargs);

struct value
builtin_os_setgid(int argc, struct value *kwargs);

struct value
builtin_os_setegid(int argc, struct value *kwargs);

struct value
builtin_os_kill(int argc, struct value *kwargs);

struct value
builtin_os_signal(int argc, struct value *kwargs);

struct value
builtin_os_exit(int argc, struct value *kwargs);

struct value
builtin_os_exec(int argc, struct value *kwargs);

struct value
builtin_errno_get(int argc, struct value *kwargs);

struct value
builtin_errno_str(int argc, struct value *kwargs);

struct value
builtin_time_time(int argc, struct value *kwargs);

struct value
builtin_time_utime(int argc, struct value *kwargs);

struct value
builtin_time_gettime(int argc, struct value *kwargs);

struct value
builtin_time_localtime(int argc, struct value *kwargs);

struct value
builtin_time_gmtime(int argc, struct value *kwargs);

struct value
builtin_time_strftime(int argc, struct value *kwargs);

struct value
builtin_time_strptime(int argc, struct value *kwargs);

struct value
builtin_stdio_fdopen(int argc, struct value *kwargs);

struct value
builtin_stdio_fileno(int argc, struct value *kwargs);

struct value
builtin_stdio_tmpfile(int argc, struct value *kwargs);

struct value
builtin_stdio_fgets(int argc, struct value *kwargs);

struct value
builtin_stdio_fread(int argc, struct value *kwargs);

struct value
builtin_stdio_read_signed(int argc, struct value *kwargs);

struct value
builtin_stdio_read_unsigned(int argc, struct value *kwargs);

struct value
builtin_stdio_read_float(int argc, struct value *kwargs);

struct value
builtin_stdio_read_double(int argc, struct value *kwargs);

struct value
builtin_stdio_write_float(int argc, struct value *kwargs);

struct value
builtin_stdio_write_double(int argc, struct value *kwargs);

struct value
builtin_stdio_write_signed(int argc, struct value *kwargs);

struct value
builtin_stdio_write_unsigned(int argc, struct value *kwargs);

struct value
builtin_stdio_puts(int argc, struct value *kwargs);

struct value
builtin_stdio_fwrite(int argc, struct value *kwargs);

struct value
builtin_stdio_fgetc(int argc, struct value *kwargs);

struct value
builtin_stdio_fputc(int argc, struct value *kwargs);

struct value
builtin_stdio_slurp(int argc, struct value *kwargs);

struct value
builtin_stdio_fflush(int argc, struct value *kwargs);

struct value
builtin_stdio_fclose(int argc, struct value *kwargs);

struct value
builtin_stdio_clearerr(int argc, struct value *kwargs);

struct value
builtin_stdio_fseek(int argc, struct value *kwargs);

struct value
builtin_stdio_ftell(int argc, struct value *kwargs);

struct value
builtin_stdio_setvbuf(int argc, struct value *kwargs);

struct value
builtin_eval(int argc, struct value *kwargs);

struct value
builtin_ty_parse(int argc, struct value *kwargs);

struct value
builtin_ty_gensym(int argc, struct value *kwargs);

struct value
builtin_ty_gc(int argc, struct value *kwargs);

struct value
builtin_ty_bt(int argc, struct value *kwargs);

struct value
builtin_token_next(int argc, struct value *kwargs);

struct value
builtin_token_peek(int argc, struct value *kwargs);

struct value
builtin_parse_source(int argc, struct value *kwargs);

struct value
builtin_parse_expr(int argc, struct value *kwargs);

struct value
builtin_parse_stmt(int argc, struct value *kwargs);

struct value
builtin_parse_fail(int argc, struct value *kwargs);

struct value
builtin_parse_show(int argc, struct value *kwargs);

struct value
builtin_lex_peek_char(int argc, struct value *kwargs);

struct value
builtin_lex_next_char(int argc, struct value *kwargs);

struct value
builtin_ty_unlock(int argc, struct value *kwargs);

struct value
builtin_ty_lock(int argc, struct value *kwargs);

struct value
builtin_ptr_typed(int argc, struct value *kwargs);

struct value
builtin_ptr_untyped(int argc, struct value *kwargs);

#endif
