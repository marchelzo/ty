CC ?= gcc-5
CFLAGS = -std=gnu11
CFLAGS += -Wall
CFLAGS += -pedantic
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

BINARIES = ty

ifdef NOLOG
        CFLAGS += -DPLUM_NO_LOG
endif

ifndef RELEASE
        CFLAGS += -fsanitize=undefined
        CFLAGS += -fsanitize=leak
        CFLAGS += -O0
else
        CFLAGS += -Ofast
        CFLAGS += -DPLUM_RELEASE
        CFLAGS += -DPLUM_NO_LOG
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

all: ty

ty: $(OBJECTS) ty.c
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ -DFILENAME=$(patsubst src/%.c,%,$<) $<

clean:
	rm -rf $(BINARIES) src/*.o

.PHONY: test.c
test.c: $(OBJECTS)
	./test.sh $(TEST_FILTER)

.PHONY: test
test: $(OBJECTS) test.c
	$(CC) $(CFLAGS) -o $@ $^
	time ./test

install: interpreter
	cp interpreter /usr/local/bin/ty
