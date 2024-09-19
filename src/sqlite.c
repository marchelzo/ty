#include <sqlite3.h>

#include "value.h"
#include "vm.h"
#include "vec.h"
#include "dict.h"

static _Thread_local int error;

static struct value
dbopen(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1 && argc != 2) {
                zP("sqlite3.open(): expected 1 or 2 arguments but got %d", argc);
        }

        struct value file = ARG(0);
        if (file.type != VALUE_STRING) {
                zP("sqlite3.open(): expected a string but got: %s", value_show(ty, &file));
        }

        int flags;
        if (argc > 1) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("sqlite3.open(): expected an integer but got: %s", value_show(ty, &ARG(1)));
                }
                flags = ARG(1).integer;
        } else {
                flags = SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE;
        }

        vec(char) s;
        vec_init(s);
        vvPn(s, file.string, file.bytes);
        vvP(s, '\0');

        sqlite3 *db;
        int r = sqlite3_open_v2(s.items, &db, flags, NULL);

        mF(s.items);

        if (r == SQLITE_OK) {
                return PTR(db);
        } else {
                sqlite3_close(db);
                error = r;
                return NIL;
        }
}

static struct value
dbclose(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.open() expects exactly 1 argument");
        }

        struct value db = ARG(0);

        if (db.type != VALUE_PTR) {
                zP("the argument to sqlite3.open() must be a pointer");
        }

        return INTEGER(sqlite3_close(db.ptr));
}

static struct value
prepare(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 2) {
                zP("sqlite3.prepare(ty) expects exactly 2 arguments");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.prepare(ty) must be a pointer");
        }

        struct value sql = ARG(1);

        if (sql.type != VALUE_STRING) {
                zP("the second argument to sqlite3.prepare(ty) must be a string");
        }

        sqlite3 *db = ptr.ptr;
        sqlite3_stmt *stmt;
        int r = sqlite3_prepare_v2(db, sql.string, sql.bytes, &stmt, NULL);

        if (r == SQLITE_OK) {
                return PTR(stmt);
        } else {
                sqlite3_finalize(stmt);
                error = r;
                return NIL;
        }
}

static struct value
step(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.step(ty) expects exactly 1 argument");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.step(ty) must be a pointer");
        }

        sqlite3_stmt *stmt = ptr.ptr;

        return INTEGER(sqlite3_step(stmt));
}

static struct value
changes(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.changes(ty) expects exactly 1 argument");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.changes(ty) must be a pointer");
        }

        sqlite3 *db = ptr.ptr;

        return INTEGER(sqlite3_changes(db));
}

static struct value
total_changes(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.totalChanges() expects exactly 1 argument");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.totalChanges() must be a pointer");
        }

        sqlite3 *db = ptr.ptr;

        return INTEGER(sqlite3_total_changes(db));
}

static struct value
column_count(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.columnCount() expects exactly 1 argument");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.columnCount() must be a pointer");
        }

        sqlite3_stmt *stmt = ptr.ptr;

        return INTEGER(sqlite3_column_count(stmt));
}

static struct value
get_column(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 2) {
                zP("sqlite3.column() expects exactly 2 arguments");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.column() must be a pointer");
        }

        struct value index = ARG(1);

        if (index.type != VALUE_INTEGER) {
                zP("the second argument to sqlite3.column() must be an integer");
        }

        int i = index.integer;
        sqlite3_stmt *stmt = ptr.ptr;
        char *s;
        int sz;
        struct blob *b;

        switch (sqlite3_column_type(stmt, i)) {
        case SQLITE_FLOAT:
                return REAL(sqlite3_column_double(stmt, i));
        case SQLITE_INTEGER:
                return INTEGER(sqlite3_column_int64(stmt, i));
        case SQLITE_TEXT:;
                s = (char *)sqlite3_column_text(stmt, i);
                sz = sqlite3_column_bytes(stmt, i);
                return vSc(s, sz);
        case SQLITE_BLOB:;
                b = value_blob_new(ty);
                NOGC(b);
                s = (char *)sqlite3_column_blob(stmt, i);
                sz = sqlite3_column_bytes(stmt, i);
                vvPn(*b, s, sz);
                return BLOB(b);
        case SQLITE_NULL:
        default:
                return NIL;
        }
}

static struct value
fetch(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.fetch(ty) expects exactly 1 argument");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.fetch(ty) must be a pointer");
        }

        sqlite3_stmt *stmt = ptr.ptr;

        char const *s;
        int sz;
        struct blob *b;
        struct value a = ARRAY(vA());
        gP(&a);

        int n = sqlite3_column_count(stmt);
        for (int i = 0; i < n; ++i) {
                switch (sqlite3_column_type(stmt, i)) {
                case SQLITE_NULL:
                        vAp(a.array, NIL);
                        break;
                case SQLITE_FLOAT:
                        vAp(a.array, REAL(sqlite3_column_double(stmt, i)));
                        break;
                case SQLITE_INTEGER:
                        vAp(a.array, INTEGER(sqlite3_column_int64(stmt, i)));
                        break;
                case SQLITE_TEXT:;
                        s = (char *)sqlite3_column_text(stmt, i);
                        sz = sqlite3_column_bytes(stmt, i);
                        vAp(a.array, vSc(s, sz));
                        break;
                case SQLITE_BLOB:;
                        b = value_blob_new(ty);
                        s = sqlite3_column_blob(stmt, i);
                        sz = sqlite3_column_bytes(stmt, i);
                        vAp(a.array, BLOB(b));
                        vvPn(*b, s, sz);
                        break;
                }
        }

        gX();

        return a;
}

static struct value
fetch_dict(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.fetch(ty) expects exactly 1 argument");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.fetch(ty) must be a pointer");
        }

        sqlite3_stmt *stmt = ptr.ptr;

        char const *s;
        int sz;
        struct blob *b;
        struct value d = DICT(dict_new(ty));
        gP(&d);

        int n = sqlite3_column_count(stmt);
        for (int i = 0; i < n; ++i) {
                char const *name = sqlite3_column_name(stmt, i);
                struct value key = vSc(name, strlen(name));
                switch (sqlite3_column_type(stmt, i)) {
                case SQLITE_NULL:
                        dict_put_value(ty, d.dict, key, NIL);
                        break;
                case SQLITE_FLOAT:
                        dict_put_value(ty, d.dict, key, REAL(sqlite3_column_double(stmt, i)));
                        break;
                case SQLITE_INTEGER:
                        dict_put_value(ty, d.dict, key, INTEGER(sqlite3_column_int64(stmt, i)));
                        break;
                case SQLITE_TEXT:;
                        s = (char *)sqlite3_column_text(stmt, i);
                        sz = sqlite3_column_bytes(stmt, i);
                        dict_put_value(ty, d.dict, key, vSc(s, sz));
                        break;
                case SQLITE_BLOB:;
                        b = value_blob_new(ty);
                        s = sqlite3_column_blob(stmt, i);
                        sz = sqlite3_column_bytes(stmt, i);
                        dict_put_value(ty, d.dict, key, BLOB(b));
                        vvPn(*b, s, sz);
                        break;
                }
        }

        gX();

        return d;
}

static struct value
finalize(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.finalize(ty) expects exactly 1 argument");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.finalize(ty) must be a pointer");
        }

        sqlite3_stmt *stmt = ptr.ptr;

        return INTEGER(sqlite3_finalize(stmt));

}

static struct value
reset(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.reset(ty) expects exactly 1 argument");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.reset(ty) must be a pointer");
        }

        sqlite3_stmt *stmt = ptr.ptr;

        return INTEGER(sqlite3_reset(stmt));
}

static struct value
mbind(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 3) {
                zP("sqlite3.bind() expects exactly 3 arguments");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.bind() must be a pointer");
        }

        int i;
        struct value index = ARG(1);

        if (index.type == VALUE_STRING) {
                vec(char) s;
                vec_init(s);
                vvPn(s, index.string, index.bytes);
                vvP(s, '\0');
                i = sqlite3_bind_parameter_index(ptr.ptr, s.items);
                vec_empty(ty, s);
        } else if (index.type == VALUE_INTEGER) {
                i = index.integer;
        } else {
                zP("the second argument to sqlite3.bind() must be an integer or string");
        }

        struct value v = ARG(2);
        sqlite3_stmt *stmt = ptr.ptr;
        int r;

        switch (v.type) {
        case VALUE_INTEGER:
                r = sqlite3_bind_int64(stmt, i, v.integer);
                break;
        case VALUE_REAL:
                r = sqlite3_bind_double(stmt, i, v.real);
                break;
        case VALUE_STRING:
                r = sqlite3_bind_text(stmt, i, v.string, v.bytes, SQLITE_TRANSIENT);
                break;
        case VALUE_BLOB:
                r = sqlite3_bind_blob(stmt, i, v.blob->items, v.blob->count, SQLITE_TRANSIENT);
                break;
        case VALUE_NIL:
                r = sqlite3_bind_null(stmt, i);
                break;
        default:
                return NIL;
        }

        return INTEGER(r);
}

static struct value
column_name(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 2) {
                zP("sqlite3.columnName() expects exactly 2 arguments");
        }

        struct value ptr = ARG(0);

        if (ptr.type != VALUE_PTR) {
                zP("the first argument to sqlite3.bind() must be a pointer");
        }

        struct value index = ARG(1);

        if (index.type != VALUE_INTEGER) {
                zP("the second argument to sqlite3.bind() must be a integer");
        }

        char const *s = sqlite3_column_name(ptr.ptr, index.integer);
        if (s == NULL) {
                return NIL;
        } else {
                return vSc(s, strlen(s));
        }
}

static struct value
error_code(Ty *ty, int argc, struct value *kwargs)
{
        if (argc == 0) {
                return INTEGER(error);
        }

        struct value v = ARG(0);

        if (v.type != VALUE_PTR) {
                zP("the argument to sqlite3.error(ty) must be a pointer");
        }

        return INTEGER(sqlite3_errcode(v.ptr));

}

static struct value
error_msg(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("sqlite3.errorMessage() expects exactly 1 argument");
        }

        struct value v = ARG(0);

        char const *s;

        if (v.type == VALUE_PTR) {
                s = sqlite3_errmsg(v.ptr);
        } else if (v.type == VALUE_INTEGER) {
                s = sqlite3_errstr(v.integer);
        } else {
                zP("the argument to sqlite3.errorMessage() must be a pointer or an integer");
        }

        return vSc(s, strlen(s));
}


#define BUILTIN(f)    { .type = VALUE_BUILTIN_FUNCTION, .builtin_function = (f), .tags = 0 }
#define INT(k)        { .type = VALUE_INTEGER,          .integer          = (k), .tags = 0 }

static struct {
        char const *name;
        struct value value;
} builtins[] = {
        { .name = "open",         .value = BUILTIN(dbopen)        },
        { .name = "close",        .value = BUILTIN(dbclose)       },
        { .name = "fetch",        .value = BUILTIN(fetch)         },
        { .name = "fetchAssoc",   .value = BUILTIN(fetch_dict)    },
        { .name = "prepare",      .value = BUILTIN(prepare)       },
        { .name = "step",         .value = BUILTIN(step)          },
        { .name = "finalize",     .value = BUILTIN(finalize)      },
        { .name = "reset",        .value = BUILTIN(reset)         },
        { .name = "bind",         .value = BUILTIN(mbind)          },
        { .name = "column",       .value = BUILTIN(get_column)    },
        { .name = "columnCount",  .value = BUILTIN(column_count)  },
        { .name = "columnName",   .value = BUILTIN(column_name)   },
        { .name = "error",        .value = BUILTIN(error_code)    },
        { .name = "errorMessage", .value = BUILTIN(error_msg)     },
        { .name = "changes",      .value = BUILTIN(changes)       },
        { .name = "totalChanges", .value = BUILTIN(total_changes) },
        { .name = "SQLITE_ABORT", .value = INT(4) },
        { .name = "SQLITE_AUTH", .value = INT(23) },
        { .name = "SQLITE_BUSY", .value = INT(5) },
        { .name = "SQLITE_CANTOPEN", .value = INT(14) },
        { .name = "SQLITE_CONSTRAINT", .value = INT(19) },
        { .name = "SQLITE_CORRUPT", .value = INT(11) },
        { .name = "SQLITE_DONE", .value = INT(101) },
        { .name = "SQLITE_EMPTY", .value = INT(16) },
        { .name = "SQLITE_ERROR", .value = INT(1) },
        { .name = "SQLITE_FORMAT", .value = INT(24) },
        { .name = "SQLITE_FULL", .value = INT(13) },
        { .name = "SQLITE_INTERNAL", .value = INT(2) },
        { .name = "SQLITE_INTERRUPT", .value = INT(9) },
        { .name = "SQLITE_IOERR", .value = INT(10) },
        { .name = "SQLITE_LOCKED", .value = INT(6) },
        { .name = "SQLITE_MISMATCH", .value = INT(20) },
        { .name = "SQLITE_MISUSE", .value = INT(21) },
        { .name = "SQLITE_NOLFS", .value = INT(22) },
        { .name = "SQLITE_NOMEM", .value = INT(7) },
        { .name = "SQLITE_NOTADB", .value = INT(26) },
        { .name = "SQLITE_NOTFOUND", .value = INT(12) },
        { .name = "SQLITE_NOTICE", .value = INT(27) },
        { .name = "SQLITE_OK", .value = INT(0) },
        { .name = "SQLITE_PERM", .value = INT(3) },
        { .name = "SQLITE_PROTOCOL", .value = INT(15) },
        { .name = "SQLITE_RANGE", .value = INT(25) },
        { .name = "SQLITE_READONLY", .value = INT(8) },
        { .name = "SQLITE_ROW", .value = INT(100) },
        { .name = "SQLITE_SCHEMA", .value = INT(17) },
        { .name = "SQLITE_TOOBIG", .value = INT(18) },
        { .name = "SQLITE_WARNING", .value = INT(28) },
        { .name = "SQLITE_ABORT_ROLLBACK", .value = INT(516) },
        { .name = "SQLITE_BUSY_RECOVERY", .value = INT(261) },
        { .name = "SQLITE_BUSY_SNAPSHOT", .value = INT(517) },
        { .name = "SQLITE_CANTOPEN_CONVPATH", .value = INT(1038) },
        { .name = "SQLITE_CANTOPEN_DIRTYWAL", .value = INT(1294) },
        { .name = "SQLITE_CANTOPEN_FULLPATH", .value = INT(782) },
        { .name = "SQLITE_CANTOPEN_ISDIR", .value = INT(526) },
        { .name = "SQLITE_CANTOPEN_NOTEMPDIR", .value = INT(270) },
        { .name = "SQLITE_CONSTRAINT_CHECK", .value = INT(275) },
        { .name = "SQLITE_CONSTRAINT_COMMITHOOK", .value = INT(531) },
        { .name = "SQLITE_CONSTRAINT_FOREIGNKEY", .value = INT(787) },
        { .name = "SQLITE_CONSTRAINT_FUNCTION", .value = INT(1043) },
        { .name = "SQLITE_CONSTRAINT_NOTNULL", .value = INT(1299) },
        { .name = "SQLITE_CONSTRAINT_PRIMARYKEY", .value = INT(1555) },
        { .name = "SQLITE_CONSTRAINT_ROWID", .value = INT(2579) },
        { .name = "SQLITE_CONSTRAINT_TRIGGER", .value = INT(1811) },
        { .name = "SQLITE_CONSTRAINT_UNIQUE", .value = INT(2067) },
        { .name = "SQLITE_CONSTRAINT_VTAB", .value = INT(2323) },
        { .name = "SQLITE_CORRUPT_SEQUENCE", .value = INT(523) },
        { .name = "SQLITE_CORRUPT_VTAB", .value = INT(267) },
        { .name = "SQLITE_ERROR_MISSING_COLLSEQ", .value = INT(257) },
        { .name = "SQLITE_ERROR_RETRY", .value = INT(513) },
        { .name = "SQLITE_ERROR_SNAPSHOT", .value = INT(769) },
        { .name = "SQLITE_IOERR_ACCESS", .value = INT(3338) },
        { .name = "SQLITE_IOERR_BLOCKED", .value = INT(2826) },
        { .name = "SQLITE_IOERR_CHECKRESERVEDLOCK", .value = INT(3594) },
        { .name = "SQLITE_IOERR_CLOSE", .value = INT(4106) },
        { .name = "SQLITE_IOERR_CONVPATH", .value = INT(6666) },
        { .name = "SQLITE_IOERR_DELETE", .value = INT(2570) },
        { .name = "SQLITE_IOERR_DELETE_NOENT", .value = INT(5898) },
        { .name = "SQLITE_IOERR_DIR_CLOSE", .value = INT(4362) },
        { .name = "SQLITE_IOERR_DIR_FSYNC", .value = INT(1290) },
        { .name = "SQLITE_IOERR_FSTAT", .value = INT(1802) },
        { .name = "SQLITE_IOERR_FSYNC", .value = INT(1034) },
        { .name = "SQLITE_IOERR_GETTEMPPATH", .value = INT(6410) },
        { .name = "SQLITE_IOERR_LOCK", .value = INT(3850) },
        { .name = "SQLITE_IOERR_MMAP", .value = INT(6154) },
        { .name = "SQLITE_IOERR_NOMEM", .value = INT(3082) },
        { .name = "SQLITE_IOERR_RDLOCK", .value = INT(2314) },
        { .name = "SQLITE_IOERR_READ", .value = INT(266) },
        { .name = "SQLITE_IOERR_SEEK", .value = INT(5642) },
        { .name = "SQLITE_IOERR_SHMLOCK", .value = INT(5130) },
        { .name = "SQLITE_IOERR_SHMMAP", .value = INT(5386) },
        { .name = "SQLITE_IOERR_SHMOPEN", .value = INT(4618) },
        { .name = "SQLITE_IOERR_SHMSIZE", .value = INT(4874) },
        { .name = "SQLITE_IOERR_SHORT_READ", .value = INT(522) },
        { .name = "SQLITE_IOERR_TRUNCATE", .value = INT(1546) },
        { .name = "SQLITE_IOERR_UNLOCK", .value = INT(2058) },
        { .name = "SQLITE_IOERR_WRITE", .value = INT(778) },
        { .name = "SQLITE_LOCKED_SHAREDCACHE", .value = INT(262) },
        { .name = "SQLITE_LOCKED_VTAB", .value = INT(518) },
        { .name = "SQLITE_NOTICE_RECOVER_ROLLBACK", .value = INT(539) },
        { .name = "SQLITE_NOTICE_RECOVER_WAL", .value = INT(283) },
        { .name = "SQLITE_OK_LOAD_PERMANENTLY", .value = INT(256) },
        { .name = "SQLITE_READONLY_CANTINIT", .value = INT(1288) },
        { .name = "SQLITE_READONLY_CANTLOCK", .value = INT(520) },
        { .name = "SQLITE_READONLY_DBMOVED", .value = INT(1032) },
        { .name = "SQLITE_READONLY_DIRECTORY", .value = INT(1544) },
        { .name = "SQLITE_READONLY_RECOVERY", .value = INT(264) },
        { .name = "SQLITE_READONLY_ROLLBACK", .value = INT(776) },
        { .name = "SQLITE_WARNING_AUTOINDEX", .value = INT(284) },
        { .name = "SQLITE_OPEN_READONLY", .value = INT(0x00000001) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_READWRITE", .value = INT(0x00000002) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_CREATE", .value = INT(0x00000004) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_DELETEONCLOSE", .value = INT(0x00000008) },  /* VFS only */
        { .name = "SQLITE_OPEN_EXCLUSIVE", .value = INT(0x00000010) },  /* VFS only */
        { .name = "SQLITE_OPEN_AUTOPROXY", .value = INT(0x00000020) },  /* VFS only */
        { .name = "SQLITE_OPEN_URI", .value = INT(0x00000040) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_MEMORY", .value = INT(0x00000080) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_MAIN_DB", .value = INT(0x00000100) },  /* VFS only */
        { .name = "SQLITE_OPEN_TEMP_DB", .value = INT(0x00000200) },  /* VFS only */
        { .name = "SQLITE_OPEN_TRANSIENT_DB", .value = INT(0x00000400) },  /* VFS only */
        { .name = "SQLITE_OPEN_MAIN_JOURNAL", .value = INT(0x00000800) },  /* VFS only */
        { .name = "SQLITE_OPEN_TEMP_JOURNAL", .value = INT(0x00001000) },  /* VFS only */
        { .name = "SQLITE_OPEN_SUBJOURNAL", .value = INT(0x00002000) },  /* VFS only */
        { .name = "SQLITE_OPEN_SUPER_JOURNAL", .value = INT(0x00004000) },  /* VFS only */
        { .name = "SQLITE_OPEN_NOMUTEX", .value = INT(0x00008000) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_FULLMUTEX", .value = INT(0x00010000) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_SHAREDCACHE", .value = INT(0x00020000) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_PRIVATECACHE", .value = INT(0x00040000) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_WAL", .value = INT(0x00080000) },  /* VFS only */
        { .name = "SQLITE_OPEN_NOFOLLOW", .value = INT(0x01000000) },  /* Ok for sqlite3_open_v2() */
        { .name = "SQLITE_OPEN_EXRESCODE", .value = INT(0x02000000) },  /* Extended result codes */
        { .name = NULL                                          }
};

void
sqlite_load(Ty *ty)
{
        vm_load_c_module(ty, "sqlite3c", builtins);
}

