#define BUILTIN(f)    { .type = VALUE_BUILTIN_FUNCTION, .builtin_function = (f), .tags = 0 }
#define FLOAT(x)      { .type = VALUE_REAL,             .real             = (x), .tags = 0 }
#define INT(k)        { .type = VALUE_INTEGER,          .integer          = (k), .tags = 0 }

{ .module = NULL,     .name = "print",             .value = BUILTIN(builtin_print)                         },
{ .module = NULL,     .name = "slurp",             .value = BUILTIN(builtin_slurp)                         },
{ .module = NULL,     .name = "die",               .value = BUILTIN(builtin_die)                           },
{ .module = NULL,     .name = "readLine",          .value = BUILTIN(builtin_read)                          },
{ .module = NULL,     .name = "rand",              .value = BUILTIN(builtin_rand)                          },
{ .module = NULL,     .name = "abs",               .value = BUILTIN(builtin_abs)                           },
{ .module = NULL,     .name = "gcd",               .value = BUILTIN(builtin_gcd)                           },
{ .module = NULL,     .name = "lcm",               .value = BUILTIN(builtin_lcm)                           },
{ .module = NULL,     .name = "round",             .value = BUILTIN(builtin_round)                         },
{ .module = NULL,     .name = "iround",            .value = BUILTIN(builtin_iround)                        },
{ .module = NULL,     .name = "ceil",              .value = BUILTIN(builtin_ceil)                          },
{ .module = NULL,     .name = "floor",             .value = BUILTIN(builtin_floor)                         },
{ .module = NULL,     .name = "int",               .value = BUILTIN(builtin_int)                           },
{ .module = NULL,     .name = "float",             .value = BUILTIN(builtin_float)                         },
{ .module = NULL,     .name = "str",               .value = BUILTIN(builtin_str)                           },
{ .module = NULL,     .name = "bool",              .value = BUILTIN(builtin_bool)                          },
{ .module = NULL,     .name = "regex",             .value = BUILTIN(builtin_regex)                         },
{ .module = NULL,     .name = "tuple",             .value = BUILTIN(builtin_tuple)                         },
{ .module = NULL,     .name = "blob",              .value = BUILTIN(builtin_blob)                          },
{ .module = NULL,     .name = "type",              .value = BUILTIN(builtin_type)                          },
{ .module = NULL,     .name = "subclass?",         .value = BUILTIN(builtin_subclass)                      },
{ .module = NULL,     .name = "members",           .value = BUILTIN(builtin_members)                       },
{ .module = NULL,     .name = "member",            .value = BUILTIN(builtin_member)                        },
{ .module = NULL,     .name = "object",            .value = BUILTIN(builtin_object)                        },
{ .module = NULL,     .name = "bindMethod",        .value = BUILTIN(builtin_bind)                          },
{ .module = NULL,     .name = "setFinalizer",      .value = BUILTIN(builtin_finalizer)                     },
{ .module = NULL,     .name = "apply",             .value = BUILTIN(builtin_apply)                         },
{ .module = NULL,     .name = "min",               .value = BUILTIN(builtin_min)                           },
{ .module = NULL,     .name = "max",               .value = BUILTIN(builtin_max)                           },
{ .module = NULL,     .name = "chr",               .value = BUILTIN(builtin_chr)                           },
{ .module = NULL,     .name = "ord",               .value = BUILTIN(builtin_ord)                           },
{ .module = NULL,     .name = "hash",              .value = BUILTIN(builtin_hash)                          },
{ .module = NULL,     .name = "md5",               .value = BUILTIN(builtin_md5)                           },
{ .module = "base64", .name = "encode",            .value = BUILTIN(builtin_base64_encode)                 },
{ .module = "base64", .name = "decode",            .value = BUILTIN(builtin_base64_decode)                 },
{ .module = NULL,     .name = "getenv",            .value = BUILTIN(builtin_getenv)                        },
{ .module = NULL,     .name = "setenv",            .value = BUILTIN(builtin_setenv)                        },
{ .module = "math",   .name = "nan?",              .value = BUILTIN(builtin_isnan)                         },
{ .module = "math",   .name = "log2",              .value = BUILTIN(builtin_log2)                          },
{ .module = "math",   .name = "log",               .value = BUILTIN(builtin_log)                           },
{ .module = "math",   .name = "exp",               .value = BUILTIN(builtin_exp)                           },
{ .module = "math",   .name = "pow",               .value = BUILTIN(builtin_pow)                           },
{ .module = "math",   .name = "sinh",              .value = BUILTIN(builtin_sinh)                          },
{ .module = "math",   .name = "cosh",              .value = BUILTIN(builtin_cosh)                          },
{ .module = "math",   .name = "tanh",              .value = BUILTIN(builtin_tanh)                          },
{ .module = "math",   .name = "asin",              .value = BUILTIN(builtin_asin)                          },
{ .module = "math",   .name = "acos",              .value = BUILTIN(builtin_acos)                          },
{ .module = "math",   .name = "atan",              .value = BUILTIN(builtin_atan)                          },
{ .module = "math",   .name = "atan2",             .value = BUILTIN(builtin_atan2)                         },
{ .module = "math",   .name = "sin",               .value = BUILTIN(builtin_sin)                           },
{ .module = "math",   .name = "cos",               .value = BUILTIN(builtin_cos)                           },
{ .module = "math",   .name = "tan",               .value = BUILTIN(builtin_tan)                           },
{ .module = "math",   .name = "sqrt",              .value = BUILTIN(builtin_sqrt)                          },
{ .module = "math",   .name = "cbrt",              .value = BUILTIN(builtin_cbrt)                          },
{ .module = "math",   .name = "pi",                .value = FLOAT(3.1415926535f)                           },
{ .module = "bit",    .name = "AND",               .value = BUILTIN(builtin_bit_and)                       },
{ .module = "bit",    .name = "OR",                .value = BUILTIN(builtin_bit_or)                        },
{ .module = "bit",    .name = "XOR",               .value = BUILTIN(builtin_bit_xor)                       },
{ .module = "bit",    .name = "complement",        .value = BUILTIN(builtin_bit_complement)                },
{ .module = "bit",    .name = "shiftLeft",         .value = BUILTIN(builtin_bit_shift_left)                },
{ .module = "bit",    .name = "shiftRight",        .value = BUILTIN(builtin_bit_shift_right)               },
#ifndef TY_WITHOUT_OS
{ .module = "os",     .name = "open",              .value = BUILTIN(builtin_os_open)                       },
{ .module = "os",     .name = "close",             .value = BUILTIN(builtin_os_close)                      },
{ .module = "os",     .name = "mktemp",            .value = BUILTIN(builtin_os_mktemp)                     },
{ .module = "os",     .name = "unlink",            .value = BUILTIN(builtin_os_unlink)                     },
{ .module = "os",     .name = "getcwd",            .value = BUILTIN(builtin_os_getcwd)                     },
{ .module = "os",     .name = "chdir",             .value = BUILTIN(builtin_os_chdir)                      },
{ .module = "os",     .name = "opendir",           .value = BUILTIN(builtin_os_opendir)                    },
{ .module = "os",     .name = "readdir",           .value = BUILTIN(builtin_os_readdir)                    },
{ .module = "os",     .name = "closedir",          .value = BUILTIN(builtin_os_closedir)                   },
{ .module = "os",     .name = "telldir",           .value = BUILTIN(builtin_os_telldir)                    },
{ .module = "os",     .name = "seekdir",           .value = BUILTIN(builtin_os_seekdir)                    },
{ .module = "os",     .name = "rewinddir",         .value = BUILTIN(builtin_os_rewinddir)                  },
{ .module = "os",     .name = "read",              .value = BUILTIN(builtin_os_read)                       },
{ .module = "os",     .name = "write",             .value = BUILTIN(builtin_os_write)                      },
{ .module = "os",     .name = "umask",             .value = BUILTIN(builtin_os_umask)                      },
{ .module = "os",     .name = "listdir",           .value = BUILTIN(builtin_os_listdir)                    },
{ .module = "os",     .name = "fcntl",             .value = BUILTIN(builtin_os_fcntl)                      },
{ .module = "os",     .name = "spawn",             .value = BUILTIN(builtin_os_spawn)                      },
{ .module = "os",     .name = "stat",              .value = BUILTIN(builtin_os_stat)                       },
{ .module = "os",     .name = "fork",              .value = BUILTIN(builtin_os_fork)                       },
{ .module = "os",     .name = "pipe",              .value = BUILTIN(builtin_os_pipe)                       },
{ .module = "os",     .name = "dup2",              .value = BUILTIN(builtin_os_dup2)                       },
{ .module = "os",     .name = "poll",              .value = BUILTIN(builtin_os_poll)                       },
{ .module = "os",     .name = "bind",              .value = BUILTIN(builtin_os_bind)                       },
{ .module = "os",     .name = "socket",            .value = BUILTIN(builtin_os_socket)                     },
{ .module = "os",     .name = "getsockopt",        .value = BUILTIN(builtin_os_getsockopt)                 },
{ .module = "os",     .name = "setsockopt",        .value = BUILTIN(builtin_os_setsockopt)                 },
{ .module = "os",     .name = "shutdown",          .value = BUILTIN(builtin_os_shutdown)                   },
{ .module = "os",     .name = "getaddrinfo",       .value = BUILTIN(builtin_os_getaddrinfo)                },
{ .module = "os",     .name = "accept",            .value = BUILTIN(builtin_os_accept)                     },
{ .module = "os",     .name = "listen",            .value = BUILTIN(builtin_os_listen)                     },
{ .module = "os",     .name = "SOCK_DGRAM",        .value = INT(SOCK_DGRAM)                                },
{ .module = "os",     .name = "SOCK_STREAM",       .value = INT(SOCK_STREAM)                               },
{ .module = "os",     .name = "SOCK_RAW",          .value = INT(SOCK_RAW)                                  },
{ .module = "os",     .name = "AF_INET",           .value = INT(AF_INET)                                   },
{ .module = "os",     .name = "AF_UNIX",           .value = INT(AF_UNIX)                                   },
{ .module = "os",     .name = "AF_UNSPEC",         .value = INT(AF_UNSPEC)                                 },
{ .module = "os",     .name = "SOL_SOCKET",        .value = INT(SOL_SOCKET)                                },
{ .module = "os",     .name = "SO_REUSEADDR",      .value = INT(SO_REUSEADDR)                              },
{ .module = "os",     .name = "SHUT_RD",           .value = INT(SHUT_RD)                                   },
{ .module = "os",     .name = "SHUT_WR",           .value = INT(SHUT_WR)                                   },
{ .module = "os",     .name = "SHUT_RDWR",         .value = INT(SHUT_RDWR)                                 },
{ .module = "os",     .name = "kill",              .value = BUILTIN(builtin_os_kill)                       },
{ .module = "os",     .name = "signal",            .value = BUILTIN(builtin_os_signal)                     },
{ .module = "os",     .name = "exit",              .value = BUILTIN(builtin_os_exit)                       },
{ .module = "os",     .name = "exec",              .value = BUILTIN(builtin_os_exec)                       },
{ .module = "os",     .name = "getpid",            .value = BUILTIN(builtin_os_getpid)                     },
{ .module = "os",     .name = "getppid",           .value = BUILTIN(builtin_os_getppid)                    },
{ .module = "os",     .name = "getuid",            .value = BUILTIN(builtin_os_getuid)                     },
{ .module = "os",     .name = "geteuid",           .value = BUILTIN(builtin_os_geteuid)                    },
{ .module = "os",     .name = "getgid",            .value = BUILTIN(builtin_os_getgid)                     },
{ .module = "os",     .name = "getegid",           .value = BUILTIN(builtin_os_getegid)                    },
{ .module = "os",     .name = "setuid",            .value = BUILTIN(builtin_os_setuid)                     },
{ .module = "os",     .name = "seteuid",           .value = BUILTIN(builtin_os_seteuid)                    },
{ .module = "os",     .name = "setgid",            .value = BUILTIN(builtin_os_setgid)                     },
{ .module = "os",     .name = "setegid",           .value = BUILTIN(builtin_os_setegid)                    },
{ .module = "os",     .name = "waitpid",           .value = BUILTIN(builtin_os_waitpid)                    },
{ .module = "os",     .name = "WIFSTOPPED",        .value = BUILTIN(builtin_os_WIFSTOPPED)                 },
{ .module = "os",     .name = "WIFEXITED",         .value = BUILTIN(builtin_os_WIFEXITED)                  },
{ .module = "os",     .name = "WEXITSTATUS",       .value = BUILTIN(builtin_os_WEXITSTATUS)                },
{ .module = "os",     .name = "WIFSIGNALED",       .value = BUILTIN(builtin_os_WIFSIGNALED)                },
{ .module = "os",     .name = "WTERMSIG",          .value = BUILTIN(builtin_os_WTERMSIG)                   },
{ .module = "os",     .name = "WSTOPSIG",          .value = BUILTIN(builtin_os_WSTOPSIG)                   },
#ifdef WCOREDUMP
{ .module = "os",     .name = "WCOREDUMP",         .value = BUILTIN(builtin_os_WCOREDUMP)                  },
#endif
#ifdef WIFCONTINUED
{ .module = "os",     .name = "WIFCONTINUED",      .value = BUILTIN(builtin_os_WIFCONTINUED)               },
#endif
{ .module = "os",     .name = "epoll_create",      .value = BUILTIN(builtin_os_epoll_create)               },
{ .module = "os",     .name = "epoll_ctl",         .value = BUILTIN(builtin_os_epoll_ctl)                  },
{ .module = "os",     .name = "epoll_wait",        .value = BUILTIN(builtin_os_epoll_wait)                 },
{ .module = "os",     .name = "EPOLL_CTL_ADD",     .value = INT(EPOLL_CTL_ADD)                             },
{ .module = "os",     .name = "EPOLL_CTL_DEL",     .value = INT(EPOLL_CTL_DEL)                             },
{ .module = "os",     .name = "EPOLL_CTL_MOD",     .value = INT(EPOLL_CTL_MOD)                             },
{ .module = "os",     .name = "EPOLLIN",           .value = INT(EPOLLIN)                                   },
{ .module = "os",     .name = "EPOLLET",           .value = INT(EPOLLET)                                   },
{ .module = "os",     .name = "EPOLLOUT",          .value = INT(EPOLLOUT)                                  },
{ .module = "os",     .name = "EPOLLHUP",          .value = INT(EPOLLHUP)                                  },
{ .module = "os",     .name = "recvfrom",          .value = BUILTIN(builtin_os_recvfrom)                   },
{ .module = "os",     .name = "sendto",            .value = BUILTIN(builtin_os_sendto)                     },
{ .module = "os",     .name = "connect",           .value = BUILTIN(builtin_os_connect)                    },
{ .module = "os",     .name = "usleep",            .value = BUILTIN(builtin_os_usleep)                     },
{ .module = "os",     .name = "POLLIN",            .value = INT(POLLIN)                                    },
{ .module = "os",     .name = "POLLOUT",           .value = INT(POLLOUT)                                   },
{ .module = "os",     .name = "POLLHUP",           .value = INT(POLLHUP)                                   },
{ .module = "os",     .name = "POLLERR",           .value = INT(POLLERR)                                   },
{ .module = "os",     .name = "POLLNVAL",          .value = INT(POLLNVAL)                                  },
{ .module = "os",     .name = "O_RDWR",            .value = INT(O_RDWR)                                    },
{ .module = "os",     .name = "O_CREAT",           .value = INT(O_CREAT)                                   },
{ .module = "os",     .name = "O_RDONLY",          .value = INT(O_RDONLY)                                  },
{ .module = "os",     .name = "O_WRONLY",          .value = INT(O_WRONLY)                                  },
{ .module = "os",     .name = "O_TRUNC",           .value = INT(O_TRUNC)                                   },
{ .module = "os",     .name = "O_APPEND",          .value = INT(O_APPEND)                                  },
{ .module = "os",     .name = "O_NONBLOCK",        .value = INT(O_NONBLOCK)                                },
{ .module = "os",     .name = "O_ASYNC",           .value = INT(O_ASYNC)                                   },
#ifdef WNOHANG
{ .module = "os",     .name = "WNOHANG",           .value = INT(WNOHANG)                                   },
#endif
#ifdef WUNTRACED
{ .module = "os",     .name = "WUNTRACED",         .value = INT(WUNTRACED)                                 },
#endif
#ifdef WCONTINUED
{ .module = "os",     .name = "WCONTINUED",        .value = INT(WCONTINUED)                                },
#endif
{ .module = "os",     .name = "F_SETFD",           .value = INT(F_SETFD)                                   },
{ .module = "os",     .name = "F_GETFD",           .value = INT(F_GETFD)                                   },
{ .module = "os",     .name = "F_GETFL",           .value = INT(F_GETFL)                                   },
{ .module = "os",     .name = "F_SETFL",           .value = INT(F_SETFL)                                   },
{ .module = "os",     .name = "F_DUPFD",           .value = INT(F_DUPFD)                                   },
{ .module = "os",     .name = "F_SETSIG",          .value = INT(F_SETSIG)                                  },
{ .module = "os",     .name = "F_GETSIG",          .value = INT(F_GETSIG)                                  },
{ .module = "os",     .name = "F_SETOWN",          .value = INT(F_SETOWN)                                  },
{ .module = "os",     .name = "F_GETOWN",          .value = INT(F_GETOWN)                                  },
#ifdef __APPLE__
{ .module = "os",     .name = "F_DUPFD_CLOEXEC",   .value = INT(F_DUPFD_CLOEXEC)                           },
{ .module = "os",     .name = "F_GETPATH",         .value = INT(F_GETPATH)                                 },
{ .module = "os",     .name = "F_PREALLOCATE",     .value = INT(F_PREALLOCATE)                             },
{ .module = "os",     .name = "F_SETSIZE",         .value = INT(F_SETSIZE)                                 },
{ .module = "os",     .name = "F_RDADVISE",        .value = INT(F_RDADVISE)                                },
{ .module = "os",     .name = "F_RDAHEAD",         .value = INT(F_RDAHEAD)                                 },
{ .module = "os",     .name = "F_NOCACHE",         .value = INT(F_NOCACHE)                                 },
{ .module = "os",     .name = "F_LOG2PHYS",        .value = INT(F_LOG2PHYS)                                },
{ .module = "os",     .name = "F_LOG2PHYS_EXT",    .value = INT(F_LOG2PHYS_EXT)                            },
{ .module = "os",     .name = "F_FULLFSYNC",       .value = INT(F_FULLFSYNC)                               },
{ .module = "os",     .name = "F_SETNOSIGPIPE",    .value = INT(F_SETNOSIGPIPE)                            },
{ .module = "os",     .name = "F_GETNOSIGPIPE",    .value = INT(F_GETNOSIGPIPE)                            },
#endif
#endif

{ .module = "thread", .name = "create",            .value = BUILTIN(builtin_thread_create)                 },
{ .module = "thread", .name = "join",              .value = BUILTIN(builtin_thread_join)                   },
{ .module = "thread", .name = "mutex",             .value = BUILTIN(builtin_thread_mutex)                  },
{ .module = "thread", .name = "destroyMutex",      .value = BUILTIN(builtin_thread_mutex_destroy)          },
{ .module = "thread", .name = "lock",              .value = BUILTIN(builtin_thread_lock)                   },
{ .module = "thread", .name = "unlock",            .value = BUILTIN(builtin_thread_unlock)                 },
{ .module = "thread", .name = "tryLock",           .value = BUILTIN(builtin_thread_trylock)                },
{ .module = "thread", .name = "cond",              .value = BUILTIN(builtin_thread_cond)                   },
{ .module = "thread", .name = "destroyCond",       .value = BUILTIN(builtin_thread_cond_destroy)           },
{ .module = "thread", .name = "waitCond",          .value = BUILTIN(builtin_thread_cond_wait)              },
{ .module = "thread", .name = "signalCond",        .value = BUILTIN(builtin_thread_cond_signal)            },
{ .module = "thread", .name = "broadcastCond",     .value = BUILTIN(builtin_thread_cond_broadcast)         },

{ .module = "stdio",  .name = "fdopen",            .value = BUILTIN(builtin_stdio_fdopen)                  },
{ .module = "stdio",  .name = "fileno",            .value = BUILTIN(builtin_stdio_fileno)                  },
{ .module = "stdio",  .name = "tmpfile",           .value = BUILTIN(builtin_stdio_tmpfile)                 },
{ .module = "stdio",  .name = "fgets",             .value = BUILTIN(builtin_stdio_fgets)                   },
{ .module = "stdio",  .name = "fread",             .value = BUILTIN(builtin_stdio_fread)                   },
{ .module = "stdio",  .name = "readSigned",        .value = BUILTIN(builtin_stdio_read_signed)             },
{ .module = "stdio",  .name = "readUnsigned",      .value = BUILTIN(builtin_stdio_read_unsigned)           },
{ .module = "stdio",  .name = "readFloat",         .value = BUILTIN(builtin_stdio_read_float)              },
{ .module = "stdio",  .name = "readDouble",        .value = BUILTIN(builtin_stdio_read_double)             },
{ .module = "stdio",  .name = "slurp",             .value = BUILTIN(builtin_stdio_slurp)                   },
{ .module = "stdio",  .name = "puts",              .value = BUILTIN(builtin_stdio_puts)                    },
{ .module = "stdio",  .name = "fwrite",            .value = BUILTIN(builtin_stdio_fwrite)                  },
{ .module = "stdio",  .name = "fgetc",             .value = BUILTIN(builtin_stdio_fgetc)                   },
{ .module = "stdio",  .name = "fputc",             .value = BUILTIN(builtin_stdio_fputc)                   },
{ .module = "stdio",  .name = "fflush",            .value = BUILTIN(builtin_stdio_fflush)                  },
{ .module = "stdio",  .name = "fclose",            .value = BUILTIN(builtin_stdio_fclose)                  },
{ .module = "stdio",  .name = "clearerr",          .value = BUILTIN(builtin_stdio_clearerr)                },
{ .module = "stdio",  .name = "fseek",             .value = BUILTIN(builtin_stdio_fseek)                   },
{ .module = "stdio",  .name = "ftell",             .value = BUILTIN(builtin_stdio_ftell)                   },
{ .module = "stdio",  .name = "setvbuf",           .value = BUILTIN(builtin_stdio_setvbuf)                 },
{ .module = "stdio",  .name = "_IOLBF",            .value = INT(_IOLBF)                                    },
{ .module = "stdio",  .name = "_IOFBF",            .value = INT(_IOFBF)                                    },
{ .module = "stdio",  .name = "_IONBF",            .value = INT(_IONBF)                                    },
{ .module = "stdio",  .name = "SEEK_SET",          .value = INT(SEEK_SET)                                  },
{ .module = "stdio",  .name = "SEEK_CUR",          .value = INT(SEEK_CUR)                                  },
{ .module = "stdio",  .name = "SEEK_END",          .value = INT(SEEK_END)                                  },
{ .module = "errno",  .name = "get",               .value = BUILTIN(builtin_errno_get)                     },
{ .module = "errno",  .name = "str",               .value = BUILTIN(builtin_errno_str)                     },
{ .module = "errno",  .name = "EACCES",            .value = INT(EACCES)                                    },
{ .module = "errno",  .name = "EAGAIN",            .value = INT(EAGAIN)                                    },
{ .module = "errno",  .name = "EBADF",             .value = INT(EBADF)                                     },
{ .module = "errno",  .name = "ENOTSOCK",          .value = INT(ENOTSOCK)                                  },
{ .module = "errno",  .name = "ETIMEDOUT",         .value = INT(ETIMEDOUT)                                 },
{ .module = "errno",  .name = "ECHILD",            .value = INT(ECHILD)                                    },
{ .module = "errno",  .name = "EDQUOT",            .value = INT(EDQUOT)                                    },
{ .module = "errno",  .name = "EEXIST",            .value = INT(EEXIST)                                    },
{ .module = "errno",  .name = "EFAULT",            .value = INT(EFAULT)                                    },
{ .module = "errno",  .name = "EFBIG",             .value = INT(EFBIG)                                     },
{ .module = "errno",  .name = "EINTR",             .value = INT(EINTR)                                     },
{ .module = "errno",  .name = "EINVAL",            .value = INT(EINVAL)                                    },
{ .module = "errno",  .name = "EISDIR",            .value = INT(EISDIR)                                    },
{ .module = "errno",  .name = "ELOOP",             .value = INT(ELOOP)                                     },
{ .module = "errno",  .name = "EMFILE",            .value = INT(EMFILE)                                    },
{ .module = "errno",  .name = "ENAMETOOLONG",      .value = INT(ENAMETOOLONG)                              },
{ .module = "errno",  .name = "ENFILE",            .value = INT(ENFILE)                                    },
{ .module = "errno",  .name = "ENODEV",            .value = INT(ENODEV)                                    },
{ .module = "errno",  .name = "ENOENT",            .value = INT(ENOENT)                                    },
{ .module = "errno",  .name = "ENOLCK",            .value = INT(ENOLCK)                                    },
{ .module = "errno",  .name = "ENOMEM",            .value = INT(ENOMEM)                                    },
{ .module = "errno",  .name = "ENOSPC",            .value = INT(ENOSPC)                                    },
{ .module = "errno",  .name = "ENOTDIR",           .value = INT(ENOTDIR)                                   },
{ .module = "errno",  .name = "ENXIO",             .value = INT(ENXIO)                                     },
{ .module = "errno",  .name = "EROFS",             .value = INT(EROFS)                                     },
{ .module = "errno",  .name = "ETXTBSY",           .value = INT(ETXTBSY)                                   },
{ .module = "errno",  .name = "EWOULDBLOCK",       .value = INT(EWOULDBLOCK)                               },
{ .module = "time",   .name = "time",              .value = BUILTIN(builtin_time_time)                     },
{ .module = "time",   .name = "utime",             .value = BUILTIN(builtin_time_utime)                    },
{ .module = "time",   .name = "localtime",         .value = BUILTIN(builtin_time_localtime)                },
{ .module = "time",   .name = "strptime",          .value = BUILTIN(builtin_time_strptime)                 },
{ .module = "time",   .name = "strftime",          .value = BUILTIN(builtin_time_strftime)                 },
{ .module = "time",   .name = "CLOCK_REALTIME",    .value = INT(CLOCK_REALTIME)                            },
#ifdef CLOCK_REALTIME_COARSE
{ .module = "time",   .name = "CLOCK_REALTIME_COARSE",  .value = INT(CLOCK_REALTIME_COARSE)                },
#endif
{ .module = "time",   .name = "CLOCK_MONOTONIC",        .value = INT(CLOCK_MONOTONIC)                      },
#ifdef CLOCK_REALTIME_COARSE
{ .module = "time",   .name = "CLOCK_MONOTONIC_COARSE", .value = INT(CLOCK_MONOTONIC_COARSE)               },
#endif
#ifdef CLOCK_PROCESS_CPUTIME_ID
{ .module = "time",   .name = "CLOCK_PROCESS_CPUTIME_ID",    .value = INT(CLOCK_PROCESS_CPUTIME_ID)                            },
#endif
#ifdef CLOCK_THREAD_CPUTIME_ID
{ .module = "time",   .name = "CLOCK_THREAD_CPUTIME_ID",    .value = INT(CLOCK_THREAD_CPUTIME_ID)                            },
#endif
#ifdef CLOCK_MONOTONIC_RAW
{ .module = "time",   .name = "CLOCK_MONOTONIC_RAW",    .value = INT(CLOCK_MONOTONIC_RAW)                            },
#endif
{ .module = "ptr",    .name = "null",              .value = POINTER(NULL)                                  },

{ .module = "json",   .name = "parse",             .value = BUILTIN(builtin_json_parse)                    },
{ .module = "json",   .name = "encode",            .value = BUILTIN(builtin_json_encode)                   },

{ .module = "gumbo",  .name = "parse",             .value = BUILTIN(html_parse)                            },
{ .module = "gumbo",  .name = "NODE_DOCUMENT",     .value = INT(0)                                         },
{ .module = "gumbo",  .name = "NODE_ELEMENT",      .value = INT(1)                                         },
{ .module = "gumbo",  .name = "NODE_TEXT",         .value = INT(2)                                         },

{ .module = "curl/core",  .name = "init",                   .value = BUILTIN(builtin_curl_init)                     },
{ .module = "curl/core",  .name = "setopt",                 .value = BUILTIN(builtin_curl_setopt)                   },
{ .module = "curl/core",  .name = "getinfo",                .value = BUILTIN(builtin_curl_getinfo)                  },
{ .module = "curl/core",  .name = "perform",                .value = BUILTIN(builtin_curl_perform)                  },
{ .module = "curl/core",  .name = "strerror",               .value = BUILTIN(builtin_curl_strerror)                 },
{ .module = "curl/core",  .name = "CURLOPT_URL",            .value = INT(CURLOPT_URL)                               },
{ .module = "curl/core",  .name = "CURLOPT_MIMEPOST",       .value = INT(CURLOPT_MIMEPOST)                          },
{ .module = "curl/core",  .name = "CURLOPT_POST",           .value = INT(CURLOPT_POST)                              },
{ .module = "curl/core",  .name = "CURLOPT_FOLLOWLOCATION", .value = INT(CURLOPT_FOLLOWLOCATION)                    },
{ .module = "curl/core",  .name = "CURLOPT_TIMEOUT",        .value = INT(CURLOPT_TIMEOUT)                           },
{ .module = "curl/core",  .name = "CURLINFO_RESPONSE_CODE", .value = INT(CURLINFO_RESPONSE_CODE)                    },
{ .module = "curl/mime",  .name = "init",                   .value = BUILTIN(builtin_curl_mime)                     },
{ .module = "curl/mime",  .name = "add",                    .value = BUILTIN(builtin_curl_mime_add)                 },
{ .module = "curl/mime",  .name = "data",                   .value = BUILTIN(builtin_curl_mime_data)                },
{ .module = "curl/mime",  .name = "name",                   .value = BUILTIN(builtin_curl_mime_name)                },
{ .module = "curl/slist", .name = "append",                 .value = BUILTIN(builtin_curl_slist_append)             },
{ .module = "curl/slist", .name = "free",                   .value = BUILTIN(builtin_curl_slist_free)               },

#ifdef SIGHUP
{ .module = "os",      .name = "SIGHUP",                 .value = INT(SIGHUP)                              },
#endif
#ifdef SIGINT
{ .module = "os",      .name = "SIGINT",                 .value = INT(SIGINT)                              },
#endif
#ifdef SIGQUIT
{ .module = "os",      .name = "SIGQUIT",                 .value = INT(SIGQUIT)                              },
#endif
#ifdef SIGILL
{ .module = "os",      .name = "SIGILL",                 .value = INT(SIGILL)                              },
#endif
#ifdef SIGTRAP
{ .module = "os",      .name = "SIGTRAP",                 .value = INT(SIGTRAP)                              },
#endif
#ifdef SIGABRT
{ .module = "os",      .name = "SIGABRT",                 .value = INT(SIGABRT)                              },
#endif
#ifdef SIGEMT
{ .module = "os",      .name = "SIGEMT",                 .value = INT(SIGEMT)                              },
#endif
#ifdef SIGFPE
{ .module = "os",      .name = "SIGFPE",                 .value = INT(SIGFPE)                              },
#endif
#ifdef SIGKILL
{ .module = "os",      .name = "SIGKILL",                 .value = INT(SIGKILL)                              },
#endif
#ifdef SIGBUS
{ .module = "os",      .name = "SIGBUS",                 .value = INT(SIGBUS)                              },
#endif
#ifdef SIGSEGV
{ .module = "os",      .name = "SIGSEGV",                 .value = INT(SIGSEGV)                              },
#endif
#ifdef SIGSYS
{ .module = "os",      .name = "SIGSYS",                 .value = INT(SIGSYS)                              },
#endif
#ifdef SIGPIPE
{ .module = "os",      .name = "SIGPIPE",                 .value = INT(SIGPIPE)                              },
#endif
#ifdef SIGALRM
{ .module = "os",      .name = "SIGALRM",                 .value = INT(SIGALRM)                              },
#endif
#ifdef SIGTERM
{ .module = "os",      .name = "SIGTERM",                 .value = INT(SIGTERM)                              },
#endif
#ifdef SIGURG
{ .module = "os",      .name = "SIGURG",                 .value = INT(SIGURG)                              },
#endif
#ifdef SIGSTOP
{ .module = "os",      .name = "SIGSTOP",                 .value = INT(SIGSTOP)                              },
#endif
#ifdef SIGTSTP
{ .module = "os",      .name = "SIGTSTP",                 .value = INT(SIGTSTP)                              },
#endif
#ifdef SIGCONT
{ .module = "os",      .name = "SIGCONT",                 .value = INT(SIGCONT)                              },
#endif
#ifdef SIGCHLD
{ .module = "os",      .name = "SIGCHLD",                 .value = INT(SIGCHLD)                              },
#endif
#ifdef SIGTTIN
{ .module = "os",      .name = "SIGTTIN",                 .value = INT(SIGTTIN)                              },
#endif
#ifdef SIGTTOU
{ .module = "os",      .name = "SIGTTOU",                 .value = INT(SIGTTOU)                              },
#endif
#ifdef SIGIO
{ .module = "os",      .name = "SIGIO",                   .value = INT(SIGIO)                                },
#endif
#ifdef SIGXCPU
{ .module = "os",      .name = "SIGXCPU",                 .value = INT(SIGXCPU)                              },
#endif
#ifdef SIGXFSZ
{ .module = "os",      .name = "SIGXFSZ",                 .value = INT(SIGXFSZ)                              },
#endif
#ifdef SIGVTALRM
{ .module = "os",      .name = "SIGVTALRM",               .value = INT(SIGVTALRM)                            },
#endif
#ifdef SIGPROF
{ .module = "os",      .name = "SIGPROF",                 .value = INT(SIGPROF)                              },
#endif
#ifdef SIGWINCH
{ .module = "os",      .name = "SIGWINCH",                .value = INT(SIGWINCH)                             },
#endif
#ifdef SIGINFO
{ .module = "os",      .name = "SIGINFO",                 .value = INT(SIGINFO)                              },
#endif
#ifdef SIGUSR1
{ .module = "os",      .name = "SIGUSR1",                 .value = INT(SIGUSR1)                              },
#endif
#ifdef SIGUSR2
{ .module = "os",      .name = "SIGUSR2",                 .value = INT(SIGUSR2)                              },
#endif

{ .module = "os",      .name = "S_IFMT",                  .value = INT(S_IFMT)                              },
{ .module = "os",      .name = "S_IFSOCK",                .value = INT(S_IFSOCK)                              },
{ .module = "os",      .name = "S_IFLNK",                 .value = INT(S_IFLNK)                              },
{ .module = "os",      .name = "S_IFREG",                 .value = INT(S_IFREG)                              },
{ .module = "os",      .name = "S_IFBLK",                 .value = INT(S_IFBLK)                              },
{ .module = "os",      .name = "S_IFDIR",                 .value = INT(S_IFDIR)                              },
{ .module = "os",      .name = "S_IFCHR",                 .value = INT(S_IFCHR)                              },
{ .module = "os",      .name = "S_IFIFO",                 .value = INT(S_IFIFO)                              },
{ .module = "os",      .name = "S_ISUID",                 .value = INT(S_ISUID)                              },
{ .module = "os",      .name = "S_ISGID",                 .value = INT(S_ISGID)                              },
{ .module = "os",      .name = "S_ISVTX",                 .value = INT(S_ISVTX)                              },
{ .module = "os",      .name = "S_IRWXU",                 .value = INT(S_IRWXU)                              },
{ .module = "os",      .name = "S_IRUSR",                 .value = INT(S_IRUSR)                              },
{ .module = "os",      .name = "S_IWUSR",                 .value = INT(S_IWUSR)                              },
{ .module = "os",      .name = "S_IXUSR",                 .value = INT(S_IXUSR)                              },
{ .module = "os",      .name = "S_IRWXG",                 .value = INT(S_IRWXG)                              },
{ .module = "os",      .name = "S_IRGRP",                 .value = INT(S_IRGRP)                              },
{ .module = "os",      .name = "S_IWGRP",                 .value = INT(S_IWGRP)                              },
{ .module = "os",      .name = "S_IXGRP",                 .value = INT(S_IXGRP)                              },
{ .module = "os",      .name = "S_IRWXO",                 .value = INT(S_IRWXO)                              },
{ .module = "os",      .name = "S_IROTH",                 .value = INT(S_IROTH)                              },
{ .module = "os",      .name = "S_IWOTH",                 .value = INT(S_IWOTH)                              },
{ .module = "os",      .name = "S_IXOTH",                 .value = INT(S_IXOTH)                              },
{ .module = "os",      .name = "DT_BLK",                  .value = INT(DT_BLK)                               },
{ .module = "os",      .name = "DT_CHR",                  .value = INT(DT_CHR)                               },
{ .module = "os",      .name = "DT_DIR",                  .value = INT(DT_DIR)                               },
{ .module = "os",      .name = "DT_FIFO",                 .value = INT(DT_FIFO)                              },
{ .module = "os",      .name = "DT_SOCK",                 .value = INT(DT_SOCK)                              },
{ .module = "os",      .name = "DT_LNK",                  .value = INT(DT_LNK)                               },
{ .module = "os",      .name = "DT_REG",                  .value = INT(DT_REG)                               },
{ .module = "os",      .name = "DT_UNKNOWN",              .value = INT(DT_UNKNOWN)                           },

{.module = "ffi", .name = "char", .value = POINTER(&ffi_type_schar)},
{.module = "ffi", .name = "short", .value = POINTER(&ffi_type_sshort)},
{.module = "ffi", .name = "int", .value = POINTER(&ffi_type_sint)},
{.module = "ffi", .name = "long", .value = POINTER(&ffi_type_slong)},
{.module = "ffi", .name = "uchar", .value = POINTER(&ffi_type_uchar)},
{.module = "ffi", .name = "ushort", .value = POINTER(&ffi_type_ushort)},
{.module = "ffi", .name = "uint", .value = POINTER(&ffi_type_uint)},
{.module = "ffi", .name = "ulong", .value = POINTER(&ffi_type_ulong)},
{.module = "ffi", .name = "u8", .value = POINTER(&ffi_type_uint8)},
{.module = "ffi", .name = "u16", .value = POINTER(&ffi_type_uint16)},
{.module = "ffi", .name = "u32", .value = POINTER(&ffi_type_uint32)},
{.module = "ffi", .name = "u64", .value = POINTER(&ffi_type_uint64)},
{.module = "ffi", .name = "i8", .value = POINTER(&ffi_type_sint8)},
{.module = "ffi", .name = "i16", .value = POINTER(&ffi_type_sint16)},
{.module = "ffi", .name = "i32", .value = POINTER(&ffi_type_sint32)},
{.module = "ffi", .name = "i64", .value = POINTER(&ffi_type_sint64)},
{.module = "ffi", .name = "float", .value = POINTER(&ffi_type_float)},
{.module = "ffi", .name = "double", .value = POINTER(&ffi_type_double)},
{.module = "ffi", .name = "ptr", .value = POINTER(&ffi_type_pointer)},
{.module = "ffi", .name = "void", .value = POINTER(&ffi_type_void)},
{.module = "ffi", .name = "new", .value = BUILTIN(cffi_new)},
{.module = "ffi", .name = "size", .value = BUILTIN(cffi_size)},
{.module = "ffi", .name = "alloc", .value = BUILTIN(cffi_alloc)},
{.module = "ffi", .name = "free", .value = BUILTIN(cffi_free)},
{.module = "ffi", .name = "addr", .value = BUILTIN(cffi_addr)},
{.module = "ffi", .name = "load", .value = BUILTIN(cffi_load)},
{.module = "ffi", .name = "store", .value = BUILTIN(cffi_store)},
{.module = "ffi", .name = "call", .value = BUILTIN(cffi_call)},
{.module = "ffi", .name = "cif", .value = BUILTIN(cffi_cif)},
{.module = "ffi", .name = "struct", .value = BUILTIN(cffi_struct)},
{.module = "ffi", .name = "dlsym", .value = BUILTIN(cffi_dlsym)},
{.module = "ffi", .name = "dlopen", .value = BUILTIN(cffi_dlopen)},
{.module = "ffi", .name = "member", .value = BUILTIN(cffi_member)},
{.module = "ffi", .name = "str", .value = BUILTIN(cffi_str)},
{.module = "ffi", .name = "blob", .value = BUILTIN(cffi_blob)},
{.module = "ffi", .name = "clone", .value = BUILTIN(cffi_clone)},
{.module = "ffi", .name = "as_str", .value = BUILTIN(cffi_as_str)},

#include "ioctl_constants.h"

#undef INT
#undef FLOAT
#undef BUILTIN

