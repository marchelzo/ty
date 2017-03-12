CC ?= gcc-5
CFLAGS = -std=c11
CFLAGS += -Wall
CFLAGS += -Iinclude
CFLAGS += -isystem/usr/local/include
CFLAGS += $(shell pcre-config --cflags)
CFLAGS += -Wno-switch
CFLAGS += -Wno-unused-value
CFLAGS += -D_GNU_SOURCE
LDFLAGS = -L/usr/local/lib
LDFLAGS = -lpthread
LDFLAGS += -lm
LDFLAGS += -lreadline
LDFLAGS += -lutf8proc
LDFLAGS += $(shell pcre-config --libs)

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
        CFLAGS += -DTY_RELEASE
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
	@echo cc $^
	@$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

%.o: %.c
	@echo cc $<
	@$(CC) $(CFLAGS) -c -o $@ -DFILENAME=$(patsubst src/%.c,%,$<) $<

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
	install -m644 lib/* $(HOME)/.ty
