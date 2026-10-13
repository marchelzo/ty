#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char *
slurp(char const *path, size_t *n)
{
        FILE *f = fopen(path, "rb");
        unsigned char *data = NULL;
        long size;

        if (f == NULL) {
                return NULL;
        }

        if (fseek(f, 0, SEEK_END) != 0 || (size = ftell(f)) < 0) {
                goto Fail;
        }

        rewind(f);

        data = malloc((size_t)size + 1);
        if (data == NULL) {
                goto Fail;
        }

        if (fread(data, 1, (size_t)size, f) != (size_t)size) {
                goto Fail;
        }

        fclose(f);
        *n = (size_t)size;

        return data;

Fail:
        free(data);
        fclose(f);
        return NULL;
}

static uint64_t
fnv(uint64_t h, void const *p, size_t n)
{
        unsigned char const *s = p;

        for (size_t i = 0; i < n; ++i) {
                h ^= s[i];
                h *= UINT64_C(0x100000001b3);
        }

        return h;
}

static void
emit(FILE *out, unsigned char const *s, size_t n)
{
        fputs("\n                \"", out);

        for (size_t i = 0; i < n; ++i) {
                unsigned char c = s[i];
                switch (c) {
                case '\\': fputs("\\\\", out);                    break;
                case '"':  fputs("\\\"", out);                    break;
                case '?':  fputs("\\?", out);                     break;
                case '\t': fputs("\\t", out);                     break;
                case '\n': fputs("\\n\"\n                \"", out); break;
                default:
                        if (c >= 0x20 && c < 0x7F) {
                                fputc(c, out);
                        } else {
                                fprintf(out, "\\%03o", c);
                        }
                }
        }

        fputc('"', out);
}

int
main(int argc, char **argv)
{
        char path[4096];
        uint64_t hash = UINT64_C(0xcbf29ce484222325);
        FILE *out;

        if (argc < 3) {
                fprintf(stderr, "usage: %s <out.c> <root> [files...]\n", argv[0]);
                return 1;
        }

        out = fopen(argv[1], "w");
        if (out == NULL) {
                fprintf(stderr, "tyembed: %s: %s\n", argv[1], strerror(errno));
                return 1;
        }

        fputs(
                "#include <stddef.h>\n"
                "\n"
                "struct embedded_file {\n"
                "        char const *path;\n"
                "        char const *data;\n"
                "        size_t      size;\n"
                "};\n"
                "\n"
                "struct embedded_file const TyEmbeddedLib[] = {\n",
                out
        );

        for (int i = 3; i < argc; ++i) {
                size_t n;
                unsigned char *data;

                snprintf(path, sizeof path, "%s/%s", argv[2], argv[i]);

                data = slurp(path, &n);
                if (data == NULL) {
                        fprintf(stderr, "tyembed: %s: %s\n", path, strerror(errno));
                        return 1;
                }

                hash = fnv(hash, argv[i], strlen(argv[i]) + 1);
                hash = fnv(hash, &n, sizeof n);
                hash = fnv(hash, data, n);

                fputs("        {\n                ", out);
                emit(out, (unsigned char const *)argv[i], strlen(argv[i]));
                fputs(",", out);
                emit(out, data, n);
                fprintf(out, ",\n                %zu\n        },\n", n);

                free(data);
        }

        fprintf(
                out,
                "        { NULL, NULL, 0 }\n"
                "};\n"
                "\n"
                "size_t const TyEmbeddedLibCount = %d;\n"
                "\n"
                "char const TyEmbeddedLibHash[] = \"%016" PRIx64 "\";\n",
                argc - 3,
                hash
        );

        if (fclose(out) != 0) {
                fprintf(stderr, "tyembed: %s: %s\n", argv[1], strerror(errno));
                return 1;
        }

        return 0;
}
