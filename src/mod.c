#include "mod.h"
#include "ty.h"
#include "table.h"

void
mod_init(TY *ty)
{
        table_init(ty->ty, &ty->pkg);
}

char const *
mod_root(Ty *ty, char const *path)
{
        char buf0[PATH_MAX + 1];
        char buf1[PATH_MAX + 1];
        char *dir = directory_of(path, buf0);

        Value const *_root = table_look(ty, &ty->ty->pkg, dir);

        if (_root != NULL) {
                return _root->ptr;
        }

        char pkg[PATH_MAX + 1];
        ConstStringVector paths = {0};

        char const *root = NULL;

        SCRATCH_SAVE();
        while (!s_eq(dir, "/")) {
                dir = S2(dir);
                svP(paths, dir);
                ty_snprintf(pkg, sizeof pkg, "%s/__pkg__.ty", dir);
                if (access(pkg, R_OK) == 0) {
                        root = dir;
                        break;
                }
                dir = directory_of(dir, buf1);
        }
        SCRATCH_RESTORE();

        if (root == NULL) {
                root = (vN(paths) > 0) ? v_0(paths) : "/";
        }

        for (int i = 0; i < vN(paths); ++i) {
                table_put(ty, &ty->ty->pkg, v__(paths, i), &PTR((void *)root));
        }

        return root;
}

/* vim: set sts=8 sw=8 expandtab: */
