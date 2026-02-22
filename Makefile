CFLAGS += -std=c2x
CFLAGS += -Wall
CFLAGS += -Iinclude
CFLAGS += -Ilibco
CFLAGS += -Idtoa
CFLAGS += -Ilibmd/include
CFLAGS += -isystem/usr/local/include
CFLAGS += $(shell pkg-config --cflags libffi)
CFLAGS += $(shell pcre2-config --cflags)
CFLAGS += -Wno-switch
CFLAGS += -Wno-unused-value
CFLAGS += -Wno-unused-function
CFLAGS += -Wno-empty-body
CFLAGS += -D_GNU_SOURCE
CFLAGS += -DPCRE2_CODE_UNIT_WIDTH=8
CFLAGS += -DCURL_STATICLIB -DPCRE2_CODE_UNIT_WIDTH=8 -DPCRE2_STATIC -DUTF8PROC_STATIC -D_GNU_SOURCE
CFLAGS += -fno-omit-frame-pointer

ifeq ($(shell uname -m),arm64)
	CFLAGS += -isystem/opt/homebrew/include
	LDFLAGS += -L/opt/homebrew/lib
	LDFLAGS += -Wl,-rpath,/opt/homebrew/lib
endif

LDFLAGS += -lm
LDFLAGS += -lcurses
LDFLAGS += -L/usr/local/lib
LDFLAGS += -lpthread

LDFLAGS += -lutf8proc
LDFLAGS += -lsqlite3
LDFLAGS += -lxxhash
LDFLAGS += -ldl
LDFLAGS += -lffi
LDFLAGS += $(shell pcre2-config --libs8)

ifndef DEBUG
	LDFLAGS += -lmimalloc
endif

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

ifdef JIT
	CFLAGS += -DTY_ENABLE_JIT
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
	CFLAGS += -DTY_RELEASE
	CFLAGS += -mcpu=native
	CFLAGS += -mtune=native
	CFLAGS += -flto
else ifdef DEBUG
	CFLAGS += -O0
	CFLAGS += -fno-omit-frame-pointer
	CFLAGS += -fno-sanitize=nonnull-attribute
	CFLAGS += -fsanitize=address
	CFLAGS += -mllvm --asan-stack=0
	CFLAGS += -fno-sanitize-address-use-after-scope
	CFLAGS += -g3
else ifdef TDEBUG
	CFLAGS += -O0
	CFLAGS += -fsanitize=thread
	CFLAGS += -ggdb3
else ifndef LOG
	CFLAGS += -Og
	CFLAGS += -g3
	CFLAGS += -DTY_RELEASE
else
	CFLAGS += -O1
endif

ifdef TY_PROFILER
	CFLAGS += -DTY_PROFILER
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

# --- Default to ncpu parallel jobs ---
NPROC := $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
MAKEFLAGS += -j$(NPROC)

# --- Auto-rebuild on config change ---
BUILD_SIG := DEBUG=$(DEBUG)|LOG=$(LOG)|JIT=$(JIT)|RELEASE=$(RELEASE)|TDEBUG=$(TDEBUG)|UNSAFE=$(UNSAFE)|LTO=$(LTO)|JEMALLOC=$(JEMALLOC)|TY_PROFILER=$(TY_PROFILER)|DEBUG_NAMES=$(DEBUG_NAMES)|PROFILE_TYPES=$(PROFILE_TYPES)|WITHOUT_OS=$(WITHOUT_OS)|GENPROF=$(GENPROF)|USEPROF=$(USEPROF)
BUILD_SIG_FILE := obj/.build_sig

PREV_SIG := $(shell cat $(BUILD_SIG_FILE) 2>/dev/null)

ifneq ($(BUILD_SIG),$(PREV_SIG))
$(shell rm -f obj/*.o obj/tyls/*.o $(PROG))
$(shell mkdir -p obj obj/tyls)
$(shell echo '$(BUILD_SIG)' > $(BUILD_SIG_FILE))
endif

# DynASM configuration
LUAJIT := luajit
DYNASM := $(LUAJIT) LuaJIT/dynasm/dynasm.lua

ifeq ($(shell uname -m),arm64)
	DYNASM_ARCH := arm64
	JIT_DASC := src/jit_arm64.dasc
	JIT_HDR  := src/jit_arm64.h
else
	DYNASM_ARCH := x64
	JIT_DASC := src/jit_x64.dasc
	JIT_HDR  := src/jit_x64.h
endif

SOURCES := $(wildcard src/*.c)
OBJECTS := $(patsubst src/%.c,obj/%.o,$(SOURCES))
TYLS_OBJECTS := $(patsubst src/%.c,obj/tyls/%.o,$(SOURCES))
EXTERNAL := libco/libco.o dtoa/dtoa.o libmd/libmd.a
ASSEMBLY := $(patsubst %.c,%.s,$(SOURCES))

all: $(PROG)

# DynASM pre-build step: generate JIT code emission header
$(JIT_HDR): $(JIT_DASC)
	@echo dynasm $<
	@$(DYNASM) -o $@ $<

include/keywords.h: src/keywords.gperf
	@echo gperf $<
	@gperf $< > $@

obj/token.o: include/keywords.h
obj/tyls/token.o: include/keywords.h

# jit.c depends on the generated DynASM header
obj/jit.o: $(JIT_HDR)
obj/tyls/jit.o: $(JIT_HDR)

ty: ty.c $(OBJECTS) $(EXTERNAL)
	@echo cc $<
	@$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

tyls: tyls.c $(TYLS_OBJECTS) $(EXTERNAL)
	@echo cc $<
	@$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

asm: $(ASSEMBLY)

%.s: src/%.c
	@echo cc $<
	$(CC) $(CFLAGS) -S -o asm/$@ -DFILENAME=$(patsubst %.c,%,$<) $<

libco/libco.o: libco/libco.c
	$(CC) $(CFLAGS) -c -o $@ -DLIBCO_MP $<

dtoa/dtoa.o: dtoa/SwiftDtoa.c
	$(CC) $(CFLAGS) -c -o $@ $<

obj/%.o: src/%.c
	@echo cc $<
	@$(CC) $(CFLAGS) -c -o $@ -DFILENAME=$(patsubst src/%.c,%,$<) $<

obj/tyls/%.o: src/%.c
	@echo cc $<
	@$(CC) $(CFLAGS) -c -o $@ -DTY_LS -DFILENAME=$(patsubst src/%.c,%,$<) $<

clean:
	rm -rf $(PROG) *.gcda $(OBJECTS) $(TYLS_OBJECTS) libco/libco.o dtoa/dtoa.o include/keywords.h $(BUILD_SIG_FILE)

test:
	./ty test.ty

install: $(PROG)
	sudo install -m755 -s $(PROG) $(DESTDIR)$(PREFIX)$(bindir)
	install -d $(HOME)/.ty
	install -m644 lib/* $(HOME)/.ty

based: $(SOURCES)
	cat $^ | gcc-13 $(CFLAGS) -c -x c -o $@ -
