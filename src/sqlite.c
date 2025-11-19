#include <sqlite3.h>

#include "value.h"
#include "vm.h"
#include "vec.h"
#include "dict.h"

static _Thread_local int error;

static Value
dbopen(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.open()", 1, 2);

        char const *path = TY_TMP_C_STR(ARGx(0, VALUE_STRING));

        int flags = (argc == 2)
                  ? INT_ARG(1)
                  : (SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE);

        sqlite3 *db;
        int err = sqlite3_open_v2(path, &db, flags, NULL);

        if (err == SQLITE_OK) {
                return PTR(db);
        } else {
                sqlite3_close(db);
                error = err;
                return NIL;
        }
}

static Value
dbclose(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.close()", 1);
        return INTEGER(sqlite3_close(PTR_ARG(0)));
}

static Value
prepare(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.perpare()", 2);

        sqlite3 *db = PTR_ARG(0);
        Value sql = ARGx(1, VALUE_STRING);

        sqlite3_stmt *stmt;
        int err = sqlite3_prepare_v2(db, (char const *)ss(sql), sN(sql), &stmt, NULL);

        if (err == SQLITE_OK) {
                return PTR(stmt);
        } else {
                sqlite3_finalize(stmt);
                error = err;
                return NIL;
        }
}

static Value
step(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.step()", 1);
        return INTEGER(sqlite3_step(PTR_ARG(0)));
}

static Value
changes(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.changes()", 1);
        return INTEGER(sqlite3_changes(PTR_ARG(0)));
}

static Value
total_changes(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.totalChanges()", 1);
        return INTEGER(sqlite3_total_changes(PTR_ARG(0)));
}

static Value
column_count(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.columnCount()", 1);
        return INTEGER(sqlite3_column_count(PTR_ARG(0)));
}

static Value
get_column(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.column()", 2);

        sqlite3_stmt *stmt = PTR_ARG(0);
        i64 i = INT_ARG(1);

        char *s;
        int sz;
        Blob *b;

        switch (sqlite3_column_type(stmt, i)) {
        case SQLITE_FLOAT:
                return REAL(sqlite3_column_double(stmt, i));
        case SQLITE_INTEGER:
                return INTEGER(sqlite3_column_int64(stmt, i));
        case SQLITE_TEXT:
                s = (char *)sqlite3_column_text(stmt, i);
                sz = sqlite3_column_bytes(stmt, i);
                return vSs(s, sz);
        case SQLITE_BLOB:;
                b = value_blob_new(ty);
                s = (char *)sqlite3_column_blob(stmt, i);
                sz = sqlite3_column_bytes(stmt, i);
                uvPn(*b, s, sz);
                return BLOB(b);
        case SQLITE_NULL:
        default:
                return NIL;
        }
}

static Value
fetch(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.fetch()", 1);

        sqlite3_stmt *stmt = PTR_ARG(0);

        char const *s;
        int sz;
        Blob *b;
        Value a = ARRAY(vA());
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
                        vAp(a.array, vSs(s, sz));
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

static Value
fetch_dict(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.fetch()", 1);

        sqlite3_stmt *stmt = PTR_ARG(0);

        char const *s;
        int sz;
        Blob *b;
        Value d = DICT(dict_new(ty));

        gP(&d);

        int n = sqlite3_column_count(stmt);
        for (int i = 0; i < n; ++i) {
                char const *name = sqlite3_column_name(stmt, i);
                Value key = vSsz(name);
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
                        dict_put_value(ty, d.dict, key, vSs(s, sz));
                        break;
                case SQLITE_BLOB:;
                        b = value_blob_new(ty);
                        s = sqlite3_column_blob(stmt, i);
                        sz = sqlite3_column_bytes(stmt, i);
                        dict_put_value(ty, d.dict, key, BLOB(b));
                        uvPn(*b, s, sz);
                        break;
                }
        }

        gX();

        return d;
}

static Value
finalize(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.finalize()", 1);
        return INTEGER(sqlite3_finalize(PTR_ARG(0)));

}

static Value
reset(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.reset()", 1);
        return INTEGER(sqlite3_reset(PTR_ARG(0)));
}

static Value
mbind(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.bind()", 3);

        sqlite3_stmt *stmt = PTR_ARG(0);
        Value index = ARGx(1, VALUE_STRING, VALUE_INTEGER);
        i32 i;

        if (index.type == VALUE_STRING) {
                i = sqlite3_bind_parameter_index(stmt, TY_TMP_C_STR(index));
        } else if (index.type == VALUE_INTEGER) {
                i = index.z;
        } else {
                UNREACHABLE();
        }

        Value v = ARG(2);
        int err;

        switch (v.type) {
        case VALUE_INTEGER:
                err = sqlite3_bind_int64(stmt, i, v.z);
                break;
        case VALUE_REAL:
                err = sqlite3_bind_double(stmt, i, v.real);
                break;
        case VALUE_STRING:
                err = sqlite3_bind_text(
                        stmt,
                        i,
                        (char const *)ss(v),
                        sN(v),
                        SQLITE_TRANSIENT
                );
                break;
        case VALUE_BLOB:
                err = sqlite3_bind_blob(
                        stmt,
                        i,
                        vv(*v.blob),
                        vN(*v.blob),
                        SQLITE_TRANSIENT
                );
                break;
        case VALUE_NIL:
                err = sqlite3_bind_null(stmt, i);
                break;
        default:
                return NIL;
        }

        return INTEGER(err);
}

static Value
column_name(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.columnName()", 2);
        sqlite3_stmt *stmt = PTR_ARG(0);
        i32 i = INT_ARG(1);
        char const *name = sqlite3_column_name(stmt, i);
        return (name != NULL) ? vSsz(name) : NIL;
}

static Value
error_code(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.error()", 0, 1);

        if (argc == 0) {
                return INTEGER(error);
        }

        return INTEGER(sqlite3_errcode(PTR_ARG(0)));

}

static Value
error_msg(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("sqlite3.errorMessage()", 1);

        Value v = ARGx(0, VALUE_PTR, VALUE_INTEGER);
        char const *msg;

        if (v.type == VALUE_PTR) {
                msg = sqlite3_errmsg(v.ptr);
        } else if (v.type == VALUE_INTEGER) {
                msg = sqlite3_errstr(v.z);
        } else {
                UNREACHABLE();
        }

        return (msg != NULL) ? vSsz(msg) : NIL;
}

#define BUILTIN(f)    { .type = VALUE_BUILTIN_FUNCTION, .builtin_function = (f), .tags = 0 }
#define INT(k)        { .type = VALUE_INTEGER,          .z                = (k), .tags = 0 }

static struct {
        char const *name;
        Value value;
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

