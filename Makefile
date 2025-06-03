CFLAGS += -std=c2x
CFLAGS += -Wall
CFLAGS += -Iinclude
CFLAGS += -Ilibco
CFLAGS += -isystem/usr/local/include
CFLAGS += $(shell pkg-config --cflags libffi)
CFLAGS += $(shell pcre2-config --cflags)
CFLAGS += $(shell pkg-config --cflags libcurl)
CFLAGS += $(shell pkg-config --cflags openssl)
CFLAGS += -Wno-switch
CFLAGS += -Wno-unused-value
CFLAGS += -Wno-unused-function
CFLAGS += -D_GNU_SOURCE
CFLAGS += -DPCRE2_CODE_UNIT_WIDTH=8
LDFLAGS += -L/usr/local/lib
LDFLAGS += -lpthread
LDFLAGS += -lm
LDFLAGS += -lreadline
LDFLAGS += -lutf8proc
LDFLAGS += -lsqlite3
LDFLAGS += -ldl
LDFLAGS += $(shell pkg-config --libs openssl)
LDFLAGS += -lffi
LDFLAGS += libco/libco.o
LDFLAGS += $(shell pcre2-config --libs8)
LDFLAGS += $(shell pkg-config --libs gumbo)
LDFLAGS += $(shell pkg-config --libs libcurl)

ifdef JEMALLOC
        LDFLAGS += -L$(shell jemalloc-config --libdir)
        LDFLAGS += -Wl,-rpath,$(shell jemalloc-config --libdir)
        LDFLAGS += -ljemalloc $(shell jemalloc-config --libs)
endif

ifdef DEBUG_NAMES
        CFLAGS += -DTY_DEBUG_NAMES
endif

ifdef PROFILE_TYPES
        CFLAGS += -DTY_PROFILE_TYPES
endif

TEST_FILTER ?= "."

PROG := ty
PREFIX ?= /usr/local

bindir := /bin

ifndef LOG
        CFLAGS += -DTY_NO_LOG
endif

ifdef UNSAFE
        CFLAGS += -DTY_UNSAFE
endif

ifdef RELEASE
        CFLAGS += -O3
        CFLAGS += -pipe
        CFLAGS += -DTY_RELEASE
        CFLAGS += -mcpu=native
        CFLAGS += -mtune=native
else ifdef DEBUG
        CFLAGS += -O0
        CFLAGS += -fsanitize=undefined
        CFLAGS += -fsanitize=address
        CFLAGS += -ggdb3
else ifdef TDEBUG
        CFLAGS += -O0
        CFLAGS += -fsanitize=thread
        CFLAGS += -ggdb3
else ifndef LOG
        CFLAGS += -O1
        CFLAGS += -ggdb3
        CFLAGS += -DTY_RELEASE
else
        CFLAGS += -O1
endif

ifdef TY_PROFILER
        CFLAGS += -DTY_ENABLE_PROFILING
endif

ifdef GENPROF
        CFLAGS += -fprofile-generate
endif

ifdef USEPROF
        CFLAGS += -fprofile-use
endif

ifdef LTO
        CFLAGS += -flto
        CFLAGS += -fomit-frame-pointer
        CFLAGS += -fwhole-program
endif

ifdef WITHOUT_OS
        CFLAGS += -DTY_WITHOUT_OS
endif

SOURCES := $(wildcard src/*.c)
OBJECTS := $(patsubst src/%.c,obj/%.o,$(SOURCES))
ASSEMBLY := $(patsubst %.c,%.s,$(SOURCES))

all: $(PROG)

ty: ty.c $(OBJECTS)
	@echo cc $^
	$(CC) $(CFLAGS) -o $@ $< obj/* $(LDFLAGS)

tyls: tyls.c $(OBJECTS)
	@echo cc $^
	$(CC) $(CFLAGS) -o $@ $< obj/* $(LDFLAGS)

asm: $(ASSEMBLY)

%.s: src/%.c
	@echo cc $<
	$(CC) $(CFLAGS) -S -o asm/$@ -DFILENAME=$(patsubst %.c,%,$<) $<

obj/%.o: src/%.c
	@echo cc $<
	$(CC) $(CFLAGS) -c -o $@ -DFILENAME=$(patsubst src/%.c,%,$<) $<

clean:
	rm -rf $(PROG) *.gcda $(wildcard obj/*.o) $(wildcard asm/*.s) $(wildcard obj/*.gcda)

test:
	./ty test.ty

install: $(PROG)
	sudo install -m755 -s $(PROG) $(DESTDIR)$(PREFIX)$(bindir)
	install -d $(HOME)/.ty
	install -m644 lib/* $(HOME)/.ty

based: $(SOURCES)
	cat $^ | gcc-13 $(CFLAGS) -c -x c -o $@ -
