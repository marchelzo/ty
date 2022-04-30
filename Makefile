CFLAGS += -std=c11
CFLAGS += -Wall
CFLAGS += -Iinclude
CFLAGS += -isystem/usr/local/include
CFLAGS += $(shell pcre-config --cflags)
CFLAGS += $(shell pkg-config --cflags libcurl)
CFLAGS += -Wno-switch
CFLAGS += -Wno-unused-value
CFLAGS += -Wno-unused-function
CFLAGS += -D_GNU_SOURCE
LDFLAGS += -L/usr/local/lib
LDFLAGS += -lpthread
LDFLAGS += -lm
LDFLAGS += -lreadline
LDFLAGS += -lutf8proc
LDFLAGS += -lsqlite3
LDFLAGS += -ldl
LDFLAGS += -lcrypto
LDFLAGS += -lffi
LDFLAGS += $(shell pcre-config --libs)
LDFLAGS += $(shell pkg-config --libs gumbo)
LDFLAGS += $(shell pkg-config --libs libcurl)

TEST_FILTER ?= "."

PROG := ty
PREFIX ?= /usr/local

bindir := /bin

ifndef LOG
        CFLAGS += -DTY_NO_LOG
endif

ifdef RELEASE
        CFLAGS += -O3
        CFLAGS += -march=native
        CFLAGS += -pipe
        CFLAGS += -DTY_RELEASE
else ifdef DEBUG
        CFLAGS += -O0
        CFLAGS += -fsanitize=undefined
        CFLAGS += -fsanitize=address
        CFLAGS += -fsanitize=leak
        CFLAGS += -ggdb3
else ifdef TDEBUG
        CFLAGS += -O0
        CFLAGS += -fsanitize=thread
        CFLAGS += -ggdb3
else
        CFLAGS += -Og
        CFLAGS += -DTY_RELEASE
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
else
        CFLAGS += -g3
endif

ifdef WITHOUT_OS
        CFLAGS += -DTY_WITHOUT_OS
endif

SOURCES := $(wildcard src/*.c)
OBJECTS := $(patsubst %.c,%.o,$(SOURCES))

all: $(PROG)

ty: $(OBJECTS) ty.c
	@echo cc $^
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

%.o: %.c
	@echo cc $<
	$(CC) $(CFLAGS) -c -o $@ -DFILENAME=$(patsubst src/%.c,%,$<) $<

clean:
	rm -rf $(PROG) *.gcda $(wildcard src/*.o) $(wildcard src/*.gcda)

test:
	./ty test.ty

install: $(PROG)
	sudo install -m755 -s $(PROG) $(DESTDIR)$(PREFIX)$(bindir)
	install -d $(HOME)/.ty
	install -m644 lib/* $(HOME)/.ty

based: $(SOURCES)
	cat $^ | gcc -c -x c -o $@ -
