#if (defined(__linux__) || defined(__APPLE__)) && !defined(TY_LS)

#if defined(__has_embed)
#if __has_embed("prof.html")
#define TY_HAVE_EMBED 1
#endif
#endif

#ifndef TY_PROF_HTML
#define TY_PROF_HTML "src/prof.html"
#endif

#ifdef TY_HAVE_EMBED

char const TyprofHtml[] = {
#embed "prof.html"
        , 0
};

#else

#ifdef __APPLE__
__asm__(
        ".section __TEXT,__const\n"
        ".globl _TyprofHtml\n"
        "_TyprofHtml:\n"
        ".incbin \"" TY_PROF_HTML "\"\n"
        ".byte 0\n"
        ".text\n"
);
#else
__asm__(
        ".section .rodata\n"
        ".global TyprofHtml\n"
        ".type TyprofHtml, @object\n"
        "TyprofHtml:\n"
        ".incbin \"" TY_PROF_HTML "\"\n"
        ".byte 0\n"
        ".size TyprofHtml, . - TyprofHtml\n"
        ".previous\n"
);
#endif

#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
