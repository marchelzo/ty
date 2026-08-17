#include "mod.h"
#include "ty.h"
#include "intern.h"

void
mod_init(TY *ty)
{
        intern_init(&ty->pkg);
}

char const *
mod_root(Ty *ty, char const *path)
{
        if (strchr(path, '/') == NULL) {
                return NULL;
        }

        char buf0[PATH_MAX + 1];
        char buf1[PATH_MAX + 1];
        char const *dir = directory_of(path, buf0);

        if (s_eq(dir, "/")) {
                return "/";
        }

        InternEntry *cached = intern_get(&ty->ty->pkg, dir);

        if (cached->id >= 0) {
                return (char const *)cached->data;
        }

        char pkg[PATH_MAX + 1];
        int_vector paths = {0};

        char const *root = NULL;

        SCRATCH_SAVE();
        while (!s_eq(dir, "/")) {
                InternEntry *entry = intern(&ty->ty->pkg, dir);
                svP(paths, entry->id);
                dir = entry->name;
                ty_snprintf(pkg, sizeof pkg, "%s/__pkg__.ty", dir);
                if (access(pkg, R_OK) == 0) {
                        root = dir;
                        break;
                }
                dir = directory_of(dir, buf1);
        }

        if (root == NULL) {
                root = intern_entry(&ty->ty->pkg, v_0(paths))->name;
        }

        for (int i = 0; i < vN(paths); ++i) {
                intern_entry(&ty->ty->pkg, v__(paths, i))->data = (void *)root;
        }
        SCRATCH_RESTORE();

        return root;
}

/* vim: set sts=8 sw=8 expandtab: */
