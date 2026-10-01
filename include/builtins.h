static struct {
        char const *module;
        char const *name;
        struct value value;
        char const *sig;
} builtins[] = {
#include "gen/builtin_table.h"
#if defined(__APPLE__)
  { .module = NULL,         .name = "__apple__",                .value = BOOL_(true)                              },
  { .module = NULL,         .name = "__windows__",              .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__linux__",                .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__bsd__",                  .value = BOOL_(false)                             },
#elif defined(__linux__)
  { .module = NULL,         .name = "__apple__",                .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__windows__",              .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__linux__",                .value = BOOL_(true)                              },
  { .module = NULL,         .name = "__bsd__",                  .value = BOOL_(false)                             },
#elif defined(_WIN32)
  { .module = NULL,         .name = "__apple__",                .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__windows__",              .value = BOOL_(true)                              },
  { .module = NULL,         .name = "__linux__",                .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__bsd__",                  .value = BOOL_(false)                             },
#elif defined(__FreeBSD__)
  { .module = NULL,         .name = "__apple__",                .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__windows__",              .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__linux__",                .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__bsd__",                  .value = BOOL_(true)                              },
#else
  { .module = NULL,         .name = "__apple__",                .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__windows__",              .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__linux__",                .value = BOOL_(false)                             },
  { .module = NULL,         .name = "__bsd__",                  .value = BOOL_(false)                             },
#endif
  { .module = "locale",     .name = "LC_ALL",                   .value = INT(LC_ALL)                              },
  { .module = "locale",     .name = "LC_COLLATE",               .value = INT(LC_COLLATE)                          },
  { .module = "locale",     .name = "LC_CTYPE",                 .value = INT(LC_CTYPE)                            },
  { .module = "math",       .name = "pi",                       .value = FLOAT(3.1415926535)                      },
  { .module = "math",       .name = "nan",                      .value = FLOAT(NAN)                               },
  { .module = "math",       .name = "inf",                      .value = FLOAT(INFINITY)                          },
#ifndef TY_WITHOUT_OS
  { .module = "os",         .name = "PATH_MAX",                 .value = INT(PATH_MAX)                            },
  { .module = "os",         .name = "NAME_MAX",                 .value = INT(NAME_MAX)                            },
  { .module = "os",         .name = "SPAWN_PIPE",               .value = INT(TY_SPAWN_PIPE)                       },
  { .module = "os",         .name = "SPAWN_NULL",               .value = INT(TY_SPAWN_NULL)                       },
  { .module = "os",         .name = "SPAWN_INHERIT",            .value = INT(TY_SPAWN_INHERIT)                    },
  { .module = "os",         .name = "SPAWN_MERGED_STDERR",      .value = INT(TY_SPAWN_MERGE_ERR)                  },

  { .module = "os",         .name = "PROT_READ",                .value = INT(PROT_READ)                           },
  { .module = "os",         .name = "PROT_WRITE",               .value = INT(PROT_WRITE)                          },
  { .module = "os",         .name = "PROT_EXEC",                .value = INT(PROT_EXEC)                           },
  { .module = "os",         .name = "PROT_NONE",                .value = INT(PROT_NONE)                           },
#if defined(MAP_ANON)
  { .module = "os",         .name = "MAP_ANON",                 .value = INT(MAP_ANON)                            },
#elif defined(MAP_ANONYMOUS)
  { .module = "os",         .name = "MAP_ANON",                 .value = INT(MAP_ANONYMOUS)                       },
#endif
  { .module = "os",         .name = "MAP_SHARED",               .value = INT(MAP_SHARED)                          },
  { .module = "os",         .name = "MAP_PRIVATE",              .value = INT(MAP_PRIVATE)                         },
  { .module = "os",         .name = "MAP_FIXED",                .value = INT(MAP_FIXED)                           },
  { .module = "os",         .name = "MAP_FAILED",               .value = POINTER(MAP_FAILED)                      },

#if defined(__linux__)
  { .module = "os",         .name = "AT_FDCWD",                 .value = INT(AT_FDCWD)                            },
  { .module = "os",         .name = "AT_SYMLINK_NOFOLLOW",      .value = INT(AT_SYMLINK_NOFOLLOW)                 },
  { .module = "os",         .name = "AT_EMPTY_PATH",            .value = INT(AT_EMPTY_PATH)                       },
#endif

  { .module = "os",         .name = "SOCK_DGRAM",               .value = INT(SOCK_DGRAM)                          },
  { .module = "os",         .name = "SOCK_STREAM",              .value = INT(SOCK_STREAM)                         },
  { .module = "os",         .name = "SOCK_RAW",                 .value = INT(SOCK_RAW)                            },
  { .module = "os",         .name = "AF_INET",                  .value = INT(AF_INET)                             },
  { .module = "os",         .name = "AF_INET6",                 .value = INT(AF_INET6)                            },
  { .module = "os",         .name = "AF_UNIX",                  .value = INT(AF_UNIX)                             },
  { .module = "os",         .name = "AF_UNSPEC",                .value = INT(AF_UNSPEC)                           },
  { .module = "os",         .name = "AI_PASSIVE",               .value = INT(AI_PASSIVE)                          },
  { .module = "os",         .name = "AI_ALL",                   .value = INT(AI_ALL)                              },
  { .module = "os",         .name = "AI_CANONNAME",             .value = INT(AI_CANONNAME)                        },
  { .module = "os",         .name = "AI_ADDRCONFIG",            .value = INT(AI_ADDRCONFIG)                       },
  { .module = "os",         .name = "AI_V4MAPPED",              .value = INT(AI_V4MAPPED)                         },
  { .module = "os",         .name = "NI_NAMEREQD",              .value = INT(NI_NAMEREQD)                         },
  { .module = "os",         .name = "NI_DGRAM",                 .value = INT(NI_DGRAM)                            },
  { .module = "os",         .name = "NI_NOFQDN",                .value = INT(NI_NOFQDN)                           },
  { .module = "os",         .name = "NI_NUMERICHOST",           .value = INT(NI_NUMERICHOST)                      },
  { .module = "os",         .name = "NI_NUMERICSERV",           .value = INT(NI_NUMERICSERV)                      },
  { .module = "os",         .name = "SOL_SOCKET",               .value = INT(SOL_SOCKET)                          },
  { .module = "os",         .name = "SO_REUSEADDR",             .value = INT(SO_REUSEADDR)                        },
  { .module = "os",         .name = "SO_LINGER",                .value = INT(SO_LINGER)                           },
  { .module = "os",         .name = "SHUT_RD",                  .value = INT(SHUT_RD)                             },
  { .module = "os",         .name = "SHUT_WR",                  .value = INT(SHUT_WR)                             },
  { .module = "os",         .name = "SHUT_RDWR",                .value = INT(SHUT_RDWR)                           },

  { .module = "os",         .name = "SIG_DFL",                  .value = INT(0)                                   },
  { .module = "os",         .name = "SIG_IGN",                  .value = INT(1)                                   },


  { .module = "os",         .name = "SIG_BLOCK",                .value = INT(SIG_BLOCK)                           },
  { .module = "os",         .name = "SIG_UNBLOCK",              .value = INT(SIG_UNBLOCK)                         },
  { .module = "os",         .name = "SIG_SETMASK",              .value = INT(SIG_SETMASK)                         },


#ifdef __linux__
  { .module = "os",         .name = "EPOLL_CTL_ADD",            .value = INT(EPOLL_CTL_ADD)                       },
  { .module = "os",         .name = "EPOLL_CTL_DEL",            .value = INT(EPOLL_CTL_DEL)                       },
  { .module = "os",         .name = "EPOLL_CTL_MOD",            .value = INT(EPOLL_CTL_MOD)                       },
  { .module = "os",         .name = "EPOLLIN",                  .value = INT(EPOLLIN)                             },
  { .module = "os",         .name = "EPOLLET",                  .value = INT(EPOLLET)                             },
  { .module = "os",         .name = "EPOLLOUT",                 .value = INT(EPOLLOUT)                            },
  { .module = "os",         .name = "EPOLLHUP",                 .value = INT(EPOLLHUP)                            },

  { .module = "os",         .name = "EFD_CLOEXEC",              .value = INT(EFD_CLOEXEC)                         },
  { .module = "os",         .name = "EFD_NONBLOCK",             .value = INT(EFD_NONBLOCK)                        },
  { .module = "os",         .name = "EFD_SEMAPHORE",            .value = INT(EFD_SEMAPHORE)                       },

  { .module = "os",         .name = "IN_ACCESS",                .value = INT(IN_ACCESS)                           },
  { .module = "os",         .name = "IN_MODIFY",                .value = INT(IN_MODIFY)                           },
  { .module = "os",         .name = "IN_ATTRIB",                .value = INT(IN_ATTRIB)                           },
  { .module = "os",         .name = "IN_CLOSE_WRITE",           .value = INT(IN_CLOSE_WRITE)                      },
  { .module = "os",         .name = "IN_CLOSE_NOWRITE",         .value = INT(IN_CLOSE_NOWRITE)                    },
  { .module = "os",         .name = "IN_OPEN",                  .value = INT(IN_OPEN)                             },
  { .module = "os",         .name = "IN_MOVED_FROM",            .value = INT(IN_MOVED_FROM)                       },
  { .module = "os",         .name = "IN_MOVED_TO",              .value = INT(IN_MOVED_TO)                         },
  { .module = "os",         .name = "IN_CREATE",                .value = INT(IN_CREATE)                           },
  { .module = "os",         .name = "IN_DELETE",                .value = INT(IN_DELETE)                           },
  { .module = "os",         .name = "IN_DELETE_SELF",           .value = INT(IN_DELETE_SELF)                      },
  { .module = "os",         .name = "IN_MOVE_SELF",             .value = INT(IN_MOVE_SELF)                        },
  { .module = "os",         .name = "IN_ALL_EVENTS",            .value = INT(IN_ALL_EVENTS)                       },
  { .module = "os",         .name = "IN_NONBLOCK",              .value = INT(IN_NONBLOCK)                         },
  { .module = "os",         .name = "IN_CLOEXEC",               .value = INT(IN_CLOEXEC)                          },

  { .module = "os",         .name = "SFD_CLOEXEC",              .value = INT(SFD_CLOEXEC)                         },
  { .module = "os",         .name = "SFD_NONBLOCK",             .value = INT(SFD_NONBLOCK)                        },

  { .module = "os",         .name = "TFD_CLOEXEC",              .value = INT(TFD_CLOEXEC)                         },
  { .module = "os",         .name = "TFD_NONBLOCK",             .value = INT(TFD_NONBLOCK)                        },
  { .module = "os",         .name = "TFD_TIMER_ABSTIME",        .value = INT(TFD_TIMER_ABSTIME)                   },
#endif

  { .module = "os",         .name = "POLLIN",                   .value = INT(POLLIN)                              },
  { .module = "os",         .name = "POLLOUT",                  .value = INT(POLLOUT)                             },
  { .module = "os",         .name = "POLLHUP",                  .value = INT(POLLHUP)                             },
  { .module = "os",         .name = "POLLERR",                  .value = INT(POLLERR)                             },
  { .module = "os",         .name = "POLLNVAL",                 .value = INT(POLLNVAL)                            },
  { .module = "os",         .name = "O_ACCMODE",                .value = INT(O_ACCMODE)                           },
  { .module = "os",         .name = "O_RDWR",                   .value = INT(O_RDWR)                              },
  { .module = "os",         .name = "O_CREAT",                  .value = INT(O_CREAT)                             },
  { .module = "os",         .name = "O_RDONLY",                 .value = INT(O_RDONLY)                            },
  { .module = "os",         .name = "O_WRONLY",                 .value = INT(O_WRONLY)                            },
  { .module = "os",         .name = "O_TRUNC",                  .value = INT(O_TRUNC)                             },
  { .module = "os",         .name = "O_APPEND",                 .value = INT(O_APPEND)                            },
  { .module = "os",         .name = "O_NONBLOCK",               .value = INT(O_NONBLOCK)                          },
  { .module = "os",         .name = "O_ASYNC",                  .value = INT(O_ASYNC)                             },
  { .module = "os",         .name = "O_DIRECTORY",              .value = INT(O_DIRECTORY)                         },
  { .module = "os",         .name = "O_EXCL",                   .value = INT(O_EXCL)                              },
  { .module = "os",         .name = "O_NOFOLLOW",               .value = INT(O_NOFOLLOW)                          },
  { .module = "os",         .name = "O_CLOEXEC",                .value = INT(O_CLOEXEC)                           },
#ifdef O_NOCTTY
  { .module = "os",         .name = "O_NOCTTY",                 .value = INT(O_NOCTTY)                            },
#endif
#ifdef O_DSYNC
  { .module = "os",         .name = "O_DSYNC",                  .value = INT(O_DSYNC)                             },
#endif
#ifdef O_RSYNC
  { .module = "os",         .name = "O_RSYNC",                  .value = INT(O_RSYNC)                             },
#endif
#ifdef O_SYNC
  { .module = "os",         .name = "O_SYNC",                   .value = INT(O_SYNC)                              },
#endif
#ifdef O_TMPFILE
  { .module = "os",         .name = "O_TMPFILE",                .value = INT(O_TMPFILE)                           },
#endif

#if defined(__APPLE__) || defined(__linux__)
  { .module = "os",         .name = "AT_FDCWD",                 .value = INT(AT_FDCWD)                          } ,
  { .module = "os",         .name = "AT_EACCESS",               .value = INT(AT_EACCESS)                        } ,
  { .module = "os",         .name = "AT_REMOVEDIR",             .value = INT(AT_REMOVEDIR)                      } ,
  { .module = "os",         .name = "AT_SYMLINK_FOLLOW",        .value = INT(AT_SYMLINK_FOLLOW)                 } ,
  { .module = "os",         .name = "AT_SYMLINK_NOFOLLOW",      .value = INT(AT_SYMLINK_NOFOLLOW)               } ,
#endif

#if defined(__linux__)
  { .module = "os",         .name = "AT_STATX_SYNC_AS_STAT",    .value = INT(AT_STATX_SYNC_AS_STAT)             } ,
  { .module = "os",         .name = "AT_STATX_FORCE_SYNC",      .value = INT(AT_STATX_FORCE_SYNC)               } ,
  { .module = "os",         .name = "AT_STATX_DONT_SYNC",       .value = INT(AT_STATX_DONT_SYNC)                } ,
  { .module = "os",         .name = "AT_RECURSIVE",             .value = INT(AT_RECURSIVE)                      } ,
  { .module = "os",         .name = "AT_EMPTY_PATH",            .value = INT(AT_EMPTY_PATH)                     } ,
  { .module = "os",         .name = "AT_NO_AUTOMOUNT",          .value = INT(AT_NO_AUTOMOUNT)                   } ,
#endif

#ifdef WNOHANG
  { .module = "os",         .name = "WNOHANG",                  .value = INT(WNOHANG)                             },
#endif
#ifdef WUNTRACED
  { .module = "os",         .name = "WUNTRACED",                .value = INT(WUNTRACED)                           },
#endif
#ifdef WCONTINUED
  { .module = "os",         .name = "WCONTINUED",               .value = INT(WCONTINUED)                          },
#endif
#ifndef _WIN32
  { .module = "os",         .name = "FD_CLOEXEC",               .value = INT(FD_CLOEXEC)                          },
#ifdef FD_CLOFORK
  { .module = "os",         .name = "FD_CLOFORK",               .value = INT(FD_CLOFORK)                          },
#endif
  { .module = "os",         .name = "F_SETFD",                  .value = INT(F_SETFD)                             },
  { .module = "os",         .name = "F_GETFD",                  .value = INT(F_GETFD)                             },
  { .module = "os",         .name = "F_GETFL",                  .value = INT(F_GETFL)                             },
  { .module = "os",         .name = "F_SETFL",                  .value = INT(F_SETFL)                             },
  { .module = "os",         .name = "F_DUPFD",                  .value = INT(F_DUPFD)                             },
  { .module = "os",         .name = "F_SETOWN",                 .value = INT(F_SETOWN)                            },
  { .module = "os",         .name = "F_GETOWN",                 .value = INT(F_GETOWN)                            },
#if defined(F_GETPATH) && defined(F_SETNOSIGPIPE)
  { .module = "os",         .name = "F_DUPFD_CLOEXEC",          .value = INT(F_DUPFD_CLOEXEC)                     },
  { .module = "os",         .name = "F_GETPATH",                .value = INT(F_GETPATH)                           },
  { .module = "os",         .name = "F_PREALLOCATE",            .value = INT(F_PREALLOCATE)                       },
  { .module = "os",         .name = "F_SETSIZE",                .value = INT(F_SETSIZE)                           },
  { .module = "os",         .name = "F_RDADVISE",               .value = INT(F_RDADVISE)                          },
  { .module = "os",         .name = "F_RDAHEAD",                .value = INT(F_RDAHEAD)                           },
  { .module = "os",         .name = "F_NOCACHE",                .value = INT(F_NOCACHE)                           },
  { .module = "os",         .name = "F_LOG2PHYS",               .value = INT(F_LOG2PHYS)                          },
  { .module = "os",         .name = "F_LOG2PHYS_EXT",           .value = INT(F_LOG2PHYS_EXT)                      },
  { .module = "os",         .name = "F_FULLFSYNC",              .value = INT(F_FULLFSYNC)                         },
  { .module = "os",         .name = "F_SETNOSIGPIPE",           .value = INT(F_SETNOSIGPIPE)                      },
  { .module = "os",         .name = "F_GETNOSIGPIPE",           .value = INT(F_GETNOSIGPIPE)                      },
#endif
#if defined(F_GETSIG) && defined(F_SETSIG)
  { .module = "os",         .name = "F_GETSIG",                 .value = INT(F_GETSIG)                            },
  { .module = "os",         .name = "F_SETSIG",                 .value = INT(F_SETSIG)                            },
#endif
#endif
#endif

#ifdef _WIN32
     #define   LOCK_SH   1    /* shared lock */
     #define   LOCK_EX   2    /* exclusive lock */
     #define   LOCK_NB   4    /* don't block when locking */
     #define   LOCK_UN   8    /* unlock */
#endif

  { .module = "os",         .name = "R_OK",                     .value = INT(R_OK)                              } ,
  { .module = "os",         .name = "W_OK",                     .value = INT(W_OK)                              } ,
  { .module = "os",         .name = "X_OK",                     .value = INT(X_OK)                              } ,
  { .module = "os",         .name = "F_OK",                     .value = INT(F_OK)                              } ,

  { .module = "os",         .name = "LOCK_SH",                  .value = INT(LOCK_SH)                             },
  { .module = "os",         .name = "LOCK_EX",                  .value = INT(LOCK_EX)                             },
  { .module = "os",         .name = "LOCK_NB",                  .value = INT(LOCK_NB)                             },
  { .module = "os",         .name = "LOCK_UN",                  .value = INT(LOCK_UN)                             },

  { .module = "os",         .name = "SEEK_SET",                 .value = INT(SEEK_SET)                            },
  { .module = "os",         .name = "SEEK_CUR",                 .value = INT(SEEK_CUR)                            },
  { .module = "os",         .name = "SEEK_END",                 .value = INT(SEEK_END)                            },
  { .module = "os",         .name = "SEEK_DATA",                .value = INT(SEEK_DATA)                           },
  { .module = "os",         .name = "SEEK_HOLE",                .value = INT(SEEK_HOLE)                           },

#if defined(__linux__)
  { .module = "os",         .name = "CLONE_CHILD_CLEARTID",     .value = INT(CLONE_CHILD_CLEARTID)                },
  { .module = "os",         .name = "CLONE_CHILD_SETTID",       .value = INT(CLONE_CHILD_SETTID)                  },
  { .module = "os",         .name = "CLONE_DETACHED",           .value = INT(CLONE_DETACHED)                      },
  { .module = "os",         .name = "CLONE_FILES",              .value = INT(CLONE_FILES)                         },
  { .module = "os",         .name = "CLONE_FS",                 .value = INT(CLONE_FS)                            },
  { .module = "os",         .name = "CLONE_IO",                 .value = INT(CLONE_IO)                            },
  { .module = "os",         .name = "CLONE_NEWCGROUP",          .value = INT(CLONE_NEWCGROUP)                     },
  { .module = "os",         .name = "CLONE_NEWIPC",             .value = INT(CLONE_NEWIPC)                        },
  { .module = "os",         .name = "CLONE_NEWNET",             .value = INT(CLONE_NEWNET)                        },
  { .module = "os",         .name = "CLONE_NEWNS",              .value = INT(CLONE_NEWNS)                         },
  { .module = "os",         .name = "CLONE_NEWPID",             .value = INT(CLONE_NEWPID)                        },
  { .module = "os",         .name = "CLONE_NEWUSER",            .value = INT(CLONE_NEWUSER)                       },
  { .module = "os",         .name = "CLONE_NEWUTS",             .value = INT(CLONE_NEWUTS)                        },
  { .module = "os",         .name = "CLONE_PARENT_SETTID",      .value = INT(CLONE_PARENT_SETTID)                 },
  { .module = "os",         .name = "CLONE_PARENT",             .value = INT(CLONE_PARENT)                        },
  { .module = "os",         .name = "CLONE_PTRACE",             .value = INT(CLONE_PTRACE)                        },
  { .module = "os",         .name = "CLONE_SETTLS",             .value = INT(CLONE_SETTLS)                        },
  { .module = "os",         .name = "CLONE_SIGHAND",            .value = INT(CLONE_SIGHAND)                       },
  { .module = "os",         .name = "CLONE_SYSVSEM",            .value = INT(CLONE_SYSVSEM)                       },
  { .module = "os",         .name = "CLONE_THREAD",             .value = INT(CLONE_THREAD)                        },
  { .module = "os",         .name = "CLONE_UNTRACED",           .value = INT(CLONE_UNTRACED)                      },
  { .module = "os",         .name = "CLONE_VFORK",              .value = INT(CLONE_VFORK)                         },
  { .module = "os",         .name = "CLONE_VM",                 .value = INT(CLONE_VM)                            },

  { .module = "os",         .name = "MNT_DETACH",               .value = INT(MNT_DETACH)                          },
  { .module = "os",         .name = "MNT_EXPIRE",               .value = INT(MNT_EXPIRE)                          },
  { .module = "os",         .name = "MNT_FORCE",                .value = INT(MNT_FORCE)                           },

  { .module = "os",         .name = "MS_BIND",                  .value = INT(MS_BIND)                             },
  { .module = "os",         .name = "MS_DIRSYNC",               .value = INT(MS_DIRSYNC)                          },
  { .module = "os",         .name = "MS_INVALIDATE",            .value = INT(MS_INVALIDATE)                       },
  { .module = "os",         .name = "MS_MANDLOCK",              .value = INT(MS_MANDLOCK)                         },
  { .module = "os",         .name = "MS_MOVE",                  .value = INT(MS_MOVE)                             },
  { .module = "os",         .name = "MS_NOATIME",               .value = INT(MS_NOATIME)                          },
  { .module = "os",         .name = "MS_NODEV",                 .value = INT(MS_NODEV)                            },
  { .module = "os",         .name = "MS_NODIRATIME",            .value = INT(MS_NODIRATIME)                       },
  { .module = "os",         .name = "MS_NOEXEC",                .value = INT(MS_NOEXEC)                           },
  { .module = "os",         .name = "MS_NOSUID",                .value = INT(MS_NOSUID)                           },
  { .module = "os",         .name = "MS_PRIVATE",               .value = INT(MS_PRIVATE)                          },
  { .module = "os",         .name = "MS_RDONLY",                .value = INT(MS_RDONLY)                           },
  { .module = "os",         .name = "MS_REC",                   .value = INT(MS_REC)                              },
  { .module = "os",         .name = "MS_RELATIME",              .value = INT(MS_RELATIME)                         },
  { .module = "os",         .name = "MS_REMOUNT",               .value = INT(MS_REMOUNT)                          },
  { .module = "os",         .name = "MS_SHARED",                .value = INT(MS_SHARED)                           },
  { .module = "os",         .name = "MS_SILENT",                .value = INT(MS_SILENT)                           },
  { .module = "os",         .name = "MS_SLAVE",                 .value = INT(MS_SLAVE)                            },
  { .module = "os",         .name = "MS_STRICTATIME",           .value = INT(MS_STRICTATIME)                      },
  { .module = "os",         .name = "MS_SYNCHRONOUS",           .value = INT(MS_SYNCHRONOUS)                      },
  { .module = "os",         .name = "MS_UNBINDABLE",            .value = INT(MS_UNBINDABLE)                       },
#endif



  { .module = "stdio",      .name = "_IOLBF",                   .value = INT(_IOLBF)                              },
  { .module = "stdio",      .name = "_IOFBF",                   .value = INT(_IOFBF)                              },
  { .module = "stdio",      .name = "_IONBF",                   .value = INT(_IONBF)                              },
  { .module = "stdio",      .name = "SEEK_SET",                 .value = INT(SEEK_SET)                            },
  { .module = "stdio",      .name = "SEEK_CUR",                 .value = INT(SEEK_CUR)                            },
  { .module = "stdio",      .name = "SEEK_END",                 .value = INT(SEEK_END)                            },
  { .module = "time",       .name = "CLOCK_REALTIME",           .value = INT(CLOCK_REALTIME)                      },
#ifdef CLOCK_REALTIME_COARSE
  { .module = "time",       .name = "CLOCK_REALTIME_COARSE",    .value = INT(CLOCK_REALTIME_COARSE)               },
#endif
  { .module = "time",       .name = "CLOCK_MONOTONIC",          .value = INT(CLOCK_MONOTONIC)                     },
#ifdef CLOCK_REALTIME_COARSE
  { .module = "time",       .name = "CLOCK_MONOTONIC_COARSE",   .value = INT(CLOCK_MONOTONIC_COARSE)              },
#endif
#ifdef CLOCK_PROCESS_CPUTIME_ID
  { .module = "time",       .name = "CLOCK_PROCESS_CPUTIME_ID", .value = INT(CLOCK_PROCESS_CPUTIME_ID)            },
#endif
#ifdef CLOCK_THREAD_CPUTIME_ID
  { .module = "time",       .name = "CLOCK_THREAD_CPUTIME_ID",  .value = INT(CLOCK_THREAD_CPUTIME_ID)             },
#endif
#ifdef CLOCK_MONOTONIC_RAW
  { .module = "time",       .name = "CLOCK_MONOTONIC_RAW",      .value = INT(CLOCK_MONOTONIC_RAW)                 },
#endif
  { .module = "ptr",        .name = "null",                     .value = POINTER(NULL)                            },

#ifdef SIGHUP
  { .module = "os",         .name = "SIGHUP",                   .value = INT(SIGHUP)                              },
#endif
#ifdef SIGINT
  { .module = "os",         .name = "SIGINT",                   .value = INT(SIGINT)                              },
#endif
#ifdef SIGQUIT
  { .module = "os",         .name = "SIGQUIT",                  .value = INT(SIGQUIT)                             },
#endif
#ifdef SIGILL
  { .module = "os",         .name = "SIGILL",                   .value = INT(SIGILL)                              },
#endif
#ifdef SIGTRAP
  { .module = "os",         .name = "SIGTRAP",                  .value = INT(SIGTRAP)                             },
#endif
#ifdef SIGABRT
  { .module = "os",         .name = "SIGABRT",                  .value = INT(SIGABRT)                             },
#endif
#ifdef SIGEMT
  { .module = "os",         .name = "SIGEMT",                   .value = INT(SIGEMT)                              },
#endif
#ifdef SIGFPE
  { .module = "os",         .name = "SIGFPE",                   .value = INT(SIGFPE)                              },
#endif
#ifdef SIGKILL
  { .module = "os",         .name = "SIGKILL",                  .value = INT(SIGKILL)                             },
#endif
#ifdef SIGBUS
  { .module = "os",         .name = "SIGBUS",                   .value = INT(SIGBUS)                              },
#endif
#ifdef SIGSEGV
  { .module = "os",         .name = "SIGSEGV",                  .value = INT(SIGSEGV)                             },
#endif
#ifdef SIGSYS
  { .module = "os",         .name = "SIGSYS",                   .value = INT(SIGSYS)                              },
#endif
#ifdef SIGPIPE
  { .module = "os",         .name = "SIGPIPE",                  .value = INT(SIGPIPE)                             },
#endif
#ifdef SIGALRM
  { .module = "os",         .name = "SIGALRM",                  .value = INT(SIGALRM)                             },
#endif
#ifdef SIGTERM
  { .module = "os",         .name = "SIGTERM",                  .value = INT(SIGTERM)                             },
#endif
#ifdef SIGURG
  { .module = "os",         .name = "SIGURG",                   .value = INT(SIGURG)                              },
#endif
#ifdef SIGSTOP
  { .module = "os",         .name = "SIGSTOP",                  .value = INT(SIGSTOP)                             },
#endif
#ifdef SIGTSTP
  { .module = "os",         .name = "SIGTSTP",                  .value = INT(SIGTSTP)                             },
#endif
#ifdef SIGCONT
  { .module = "os",         .name = "SIGCONT",                  .value = INT(SIGCONT)                             },
#endif
#ifdef SIGCHLD
  { .module = "os",         .name = "SIGCHLD",                  .value = INT(SIGCHLD)                             },
#endif
#ifdef SIGTTIN
  { .module = "os",         .name = "SIGTTIN",                  .value = INT(SIGTTIN)                             },
#endif
#ifdef SIGTTOU
  { .module = "os",         .name = "SIGTTOU",                  .value = INT(SIGTTOU)                             },
#endif
#ifdef SIGIO
  { .module = "os",         .name = "SIGIO",                    .value = INT(SIGIO)                               },
#endif
#ifdef RLIMIT_CPU
  { .module = "os",         .name = "RLIMIT_CPU",               .value = INT(RLIMIT_CPU)                          },
#endif
#ifdef RLIMIT_FSIZE
  { .module = "os",         .name = "RLIMIT_FSIZE",             .value = INT(RLIMIT_FSIZE)                        },
#endif
#ifdef RLIMIT_DATA
  { .module = "os",         .name = "RLIMIT_DATA",              .value = INT(RLIMIT_DATA)                         },
#endif
#ifdef RLIMIT_STACK
  { .module = "os",         .name = "RLIMIT_STACK",             .value = INT(RLIMIT_STACK)                        },
#endif
#ifdef RLIMIT_CORE
  { .module = "os",         .name = "RLIMIT_CORE",              .value = INT(RLIMIT_CORE)                         },
#endif
#ifdef RLIMIT_RSS
  { .module = "os",         .name = "RLIMIT_RSS",               .value = INT(RLIMIT_RSS)                          },
#endif
#ifdef RLIMIT_NPROC
  { .module = "os",         .name = "RLIMIT_NPROC",             .value = INT(RLIMIT_NPROC)                        },
#endif
#ifdef RLIMIT_NOFILE
  { .module = "os",         .name = "RLIMIT_NOFILE",            .value = INT(RLIMIT_NOFILE)                       },
#endif
#ifdef RLIMIT_MEMLOCK
  { .module = "os",         .name = "RLIMIT_MEMLOCK",           .value = INT(RLIMIT_MEMLOCK)                      },
#endif
#ifdef RLIMIT_AS
  { .module = "os",         .name = "RLIMIT_AS",                .value = INT(RLIMIT_AS)                           },
#endif
#ifdef RLIMIT_LOCKS
  { .module = "os",         .name = "RLIMIT_LOCKS",             .value = INT(RLIMIT_LOCKS)                        },
#endif
#ifdef RLIMIT_SIGPENDING
  { .module = "os",         .name = "RLIMIT_SIGPENDING",        .value = INT(RLIMIT_SIGPENDING)                   },
#endif
#ifdef RLIMIT_MSGQUEUE
  { .module = "os",         .name = "RLIMIT_MSGQUEUE",          .value = INT(RLIMIT_MSGQUEUE)                     },
#endif
#ifdef RLIMIT_NICE
  { .module = "os",         .name = "RLIMIT_NICE",              .value = INT(RLIMIT_NICE)                         },
#endif
#ifdef RLIMIT_RTPRIO
  { .module = "os",         .name = "RLIMIT_RTPRIO",            .value = INT(RLIMIT_RTPRIO)                       },
#endif
#ifdef RLIMIT_RTTIME
  { .module = "os",         .name = "RLIMIT_RTTIME",            .value = INT(RLIMIT_RTTIME)                       },
#endif
#ifdef RLIM_INFINITY
  { .module = "os",         .name = "RLIM_INFINITY",            .value = INT((imax)RLIM_INFINITY)                 },
#endif
#ifdef SIGXCPU
  { .module = "os",         .name = "SIGXCPU",                  .value = INT(SIGXCPU)                             },
#endif
#ifdef SIGXFSZ
  { .module = "os",         .name = "SIGXFSZ",                  .value = INT(SIGXFSZ)                             },
#endif
#ifdef SIGVTALRM
  { .module = "os",         .name = "SIGVTALRM",                .value = INT(SIGVTALRM)                           },
#endif
#ifdef SIGPROF
  { .module = "os",         .name = "SIGPROF",                  .value = INT(SIGPROF)                             },
#endif
#ifdef SIGWINCH
  { .module = "os",         .name = "SIGWINCH",                 .value = INT(SIGWINCH)                            },
#endif
#ifdef SIGINFO
  { .module = "os",         .name = "SIGINFO",                  .value = INT(SIGINFO)                             },
#endif
#ifdef SIGUSR1
  { .module = "os",         .name = "SIGUSR1",                  .value = INT(SIGUSR1)                             },
#endif
#ifdef SIGUSR2
  { .module = "os",         .name = "SIGUSR2",                  .value = INT(SIGUSR2)                             },
#endif

  { .module = "os",         .name = "NSIG",                      .value = INT(32)                                 },

  { .module = "os",         .name = "S_IFREG",                  .value = INT(S_IFREG)                             },
  { .module = "os",         .name = "S_IFDIR",                  .value = INT(S_IFDIR)                             },
#ifndef _WIN32
  { .module = "os",         .name = "S_IFMT",                   .value = INT(S_IFMT)                              },
  { .module = "os",         .name = "S_IFSOCK",                 .value = INT(S_IFSOCK)                            },
  { .module = "os",         .name = "S_IFLNK",                  .value = INT(S_IFLNK)                             },
  { .module = "os",         .name = "S_IFBLK",                  .value = INT(S_IFBLK)                             },
  { .module = "os",         .name = "S_IFCHR",                  .value = INT(S_IFCHR)                             },
  { .module = "os",         .name = "S_IFIFO",                  .value = INT(S_IFIFO)                             },
  { .module = "os",         .name = "S_ISUID",                  .value = INT(S_ISUID)                             },
  { .module = "os",         .name = "S_ISGID",                  .value = INT(S_ISGID)                             },
  { .module = "os",         .name = "S_ISVTX",                  .value = INT(S_ISVTX)                             },
  { .module = "os",         .name = "S_IRWXU",                  .value = INT(S_IRWXU)                             },
  { .module = "os",         .name = "S_IRUSR",                  .value = INT(S_IRUSR)                             },
  { .module = "os",         .name = "S_IWUSR",                  .value = INT(S_IWUSR)                             },
  { .module = "os",         .name = "S_IXUSR",                  .value = INT(S_IXUSR)                             },
  { .module = "os",         .name = "S_IRWXG",                  .value = INT(S_IRWXG)                             },
  { .module = "os",         .name = "S_IRGRP",                  .value = INT(S_IRGRP)                             },
  { .module = "os",         .name = "S_IWGRP",                  .value = INT(S_IWGRP)                             },
  { .module = "os",         .name = "S_IXGRP",                  .value = INT(S_IXGRP)                             },
  { .module = "os",         .name = "S_IRWXO",                  .value = INT(S_IRWXO)                             },
  { .module = "os",         .name = "S_IROTH",                  .value = INT(S_IROTH)                             },
  { .module = "os",         .name = "S_IWOTH",                  .value = INT(S_IWOTH)                             },
  { .module = "os",         .name = "S_IXOTH",                  .value = INT(S_IXOTH)                             },
  { .module = "os",         .name = "DT_BLK",                   .value = INT(DT_BLK)                              },
  { .module = "os",         .name = "DT_CHR",                   .value = INT(DT_CHR)                              },
  { .module = "os",         .name = "DT_DIR",                   .value = INT(DT_DIR)                              },
  { .module = "os",         .name = "DT_FIFO",                  .value = INT(DT_FIFO)                             },
  { .module = "os",         .name = "DT_SOCK",                  .value = INT(DT_SOCK)                             },
  { .module = "os",         .name = "DT_LNK",                   .value = INT(DT_LNK)                              },
  { .module = "os",         .name = "DT_REG",                   .value = INT(DT_REG)                              },
  { .module = "os",         .name = "DT_UNKNOWN",               .value = INT(DT_UNKNOWN)                          },
#endif

#ifndef _WIN32
  { .module = "termios",    .name = "CSIZE",                    .value = INT(CSIZE)                               },
  { .module = "termios",    .name = "CS5",                      .value = INT(CS5)                                 },
  { .module = "termios",    .name = "CS6",                      .value = INT(CS6)                                 },
  { .module = "termios",    .name = "CS7",                      .value = INT(CS7)                                 },
  { .module = "termios",    .name = "CS8",                      .value = INT(CS8)                                 },
  { .module = "termios",    .name = "CSTOPB",                   .value = INT(CSTOPB)                              },
  { .module = "termios",    .name = "CREAD",                    .value = INT(CREAD)                               },
  { .module = "termios",    .name = "PARENB",                   .value = INT(PARENB)                              },
  { .module = "termios",    .name = "PARODD",                   .value = INT(PARODD)                              },
  { .module = "termios",    .name = "HUPCL",                    .value = INT(HUPCL)                               },
  { .module = "termios",    .name = "CLOCAL",                   .value = INT(CLOCAL)                              },
  { .module = "termios",    .name = "IGNBRK",                   .value = INT(IGNBRK)                              },
  { .module = "termios",    .name = "BRKINT",                   .value = INT(BRKINT)                              },
  { .module = "termios",    .name = "IGNPAR",                   .value = INT(IGNPAR)                              },
  { .module = "termios",    .name = "PARMRK",                   .value = INT(PARMRK)                              },
  { .module = "termios",    .name = "INPCK",                    .value = INT(INPCK)                               },
  { .module = "termios",    .name = "ISTRIP",                   .value = INT(ISTRIP)                              },
  { .module = "termios",    .name = "INLCR",                    .value = INT(INLCR)                               },
  { .module = "termios",    .name = "IGNCR",                    .value = INT(IGNCR)                               },
  { .module = "termios",    .name = "ICRNL",                    .value = INT(ICRNL)                               },
  { .module = "termios",    .name = "IXON",                     .value = INT(IXON)                                },
  { .module = "termios",    .name = "IXANY",                    .value = INT(IXANY)                               },
  { .module = "termios",    .name = "IXOFF",                    .value = INT(IXOFF)                               },
  { .module = "termios",    .name = "IMAXBEL",                  .value = INT(IMAXBEL)                             },
  { .module = "termios",    .name = "IUTF8",                    .value = INT(IUTF8)                               },
  { .module = "termios",    .name = "OPOST",                    .value = INT(OPOST)                               },
  { .module = "termios",    .name = "ONLCR",                    .value = INT(ONLCR)                               },
  { .module = "termios",    .name = "OCRNL",                    .value = INT(OCRNL)                               },
  { .module = "termios",    .name = "ONOCR",                    .value = INT(ONOCR)                               },
  { .module = "termios",    .name = "ONLRET",                   .value = INT(ONLRET)                              },
#if defined(OFILL) && defined(OFDEL)
  { .module = "termios",    .name = "OFILL",                    .value = INT(OFILL)                               },
  { .module = "termios",    .name = "OFDEL",                    .value = INT(OFDEL)                               },
#endif
#if defined(VTDLY) && defined(VT0) && defined(VT1)
  { .module = "termios",    .name = "VTDLY",                    .value = INT(VTDLY)                               },
  { .module = "termios",    .name = "VT0",                      .value = INT(VT0)                                 },
  { .module = "termios",    .name = "VT1",                      .value = INT(VT1)                                 },
#endif
  { .module = "termios",    .name = "B0",                       .value = INT(B0)                                  },
  { .module = "termios",    .name = "B50",                      .value = INT(B50)                                 },
  { .module = "termios",    .name = "B75",                      .value = INT(B75)                                 },
  { .module = "termios",    .name = "B110",                     .value = INT(B110)                                },
  { .module = "termios",    .name = "B134",                     .value = INT(B134)                                },
  { .module = "termios",    .name = "B150",                     .value = INT(B150)                                },
  { .module = "termios",    .name = "B200",                     .value = INT(B200)                                },
  { .module = "termios",    .name = "B300",                     .value = INT(B300)                                },
  { .module = "termios",    .name = "B600",                     .value = INT(B600)                                },
  { .module = "termios",    .name = "B1200",                    .value = INT(B1200)                               },
  { .module = "termios",    .name = "B1800",                    .value = INT(B1800)                               },
  { .module = "termios",    .name = "B2400",                    .value = INT(B2400)                               },
  { .module = "termios",    .name = "B4800",                    .value = INT(B4800)                               },
  { .module = "termios",    .name = "B9600",                    .value = INT(B9600)                               },
  { .module = "termios",    .name = "B19200",                   .value = INT(B19200)                              },
  { .module = "termios",    .name = "B38400",                   .value = INT(B38400)                              },
  { .module = "termios",    .name = "TCOOFF",                   .value = INT(TCOOFF)                              },
  { .module = "termios",    .name = "TCOON",                    .value = INT(TCOON)                               },
  { .module = "termios",    .name = "TCIOFF",                   .value = INT(TCIOFF)                              },
  { .module = "termios",    .name = "TCION",                    .value = INT(TCION)                               },
  { .module = "termios",    .name = "TCIFLUSH",                 .value = INT(TCIFLUSH)                            },
  { .module = "termios",    .name = "TCOFLUSH",                 .value = INT(TCOFLUSH)                            },
  { .module = "termios",    .name = "TCIOFLUSH",                .value = INT(TCIOFLUSH)                           },
  { .module = "termios",    .name = "ISIG",                     .value = INT(ISIG)                                },
  { .module = "termios",    .name = "ICANON",                   .value = INT(ICANON)                              },
  { .module = "termios",    .name = "ECHO",                     .value = INT(ECHO)                                },
  { .module = "termios",    .name = "ECHOE",                    .value = INT(ECHOE)                               },
  { .module = "termios",    .name = "ECHOK",                    .value = INT(ECHOK)                               },
  { .module = "termios",    .name = "ECHONL",                   .value = INT(ECHONL)                              },
  { .module = "termios",    .name = "NOFLSH",                   .value = INT(NOFLSH)                              },
  { .module = "termios",    .name = "TOSTOP",                   .value = INT(TOSTOP)                              },
  { .module = "termios",    .name = "IEXTEN",                   .value = INT(IEXTEN)                              },
  { .module = "termios",    .name = "TCSANOW",                  .value = INT(TCSANOW)                             },
  { .module = "termios",    .name = "TCSADRAIN",                .value = INT(TCSADRAIN)                           },
  { .module = "termios",    .name = "TCSAFLUSH",                .value = INT(TCSAFLUSH)                           },
  { .module = "termios",    .name = "VMIN",                     .value = INT(VMIN)                                },
  { .module = "termios",    .name = "VTIME",                    .value = INT(VTIME)                               },
#endif

  { .module = "ty",         .name = "valueSize",                .value = INT(sizeof (Value))                      },







#ifndef _WIN32
  #include "ioctl_constants.h"
#endif

#include "errno_constants.h"


};
