CC ?= gcc-5
CFLAGS = -std=gnu11
CFLAGS += -Wall
CFLAGS += -Iinclude
CFLAGS += -isystem/usr/local/include
CFLAGS += $(shell pcre-config --cflags)
CFLAGS += $(shell pcre-config --libs)
CFLAGS += -lpthread
CFLAGS += -lm
CFLAGS += -L/usr/local/lib
CFLAGS += -lreadline
CFLAGS += -lutf8proc
CFLAGS += -Wno-switch
CFLAGS += -Wno-unused-value

TEST_FILTER ?= "."

PROG := ty
PREFIX ?= /usr/local

bindir := /bin

ifdef NOLOG
        CFLAGS += -DTY_NO_LOG
endif

ifndef RELEASE
        CFLAGS += -fsanitize=undefined
        CFLAGS += -fsanitize=leak
        CFLAGS += -O0
else
        CFLAGS += -Ofast
        CFLAGS += -DPTY_RELEASE
        CFLAGS += -DTY_NO_LOG
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
        CFLAGS += -ggdb3
endif

SOURCES := $(wildcard src/*.c)
OBJECTS := $(patsubst %.c,%.o,$(SOURCES))

all: $(PROG)

ty: $(OBJECTS) ty.c
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ -DFILENAME=$(patsubst src/%.c,%,$<) $<

clean:
	rm -rf $(PROG) src/*.o

.PHONY: test.c
test.c: $(OBJECTS)
	./test.sh $(TEST_FILTER)

.PHONY: test
test: $(OBJECTS) test.c
	$(CC) $(CFLAGS) -o $@ $^
	time ./test

install: $(PROG)
	install -m755 -s $(PROG) $(DESTDIR)$(PREFIX)$(bindir)
	install -d $(HOME)/.ty
	install -m644 prelude.ty $(HOME)/.ty
