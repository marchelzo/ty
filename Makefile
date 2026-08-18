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

ifeq ($(shell uname -s),Darwin)
	LDFLAGS += -framework Accelerate
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

ifdef BOX_STATS
	CFLAGS += -DTY_BOX_STATS
endif

ifdef NO_JIT
	CFLAGS += -DTY_NO_JIT
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
	CFLAGS += -O0
	CFLAGS += -g
	CFLAGS += -DTY_RELEASE
else
	CFLAGS += -O1
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

ifndef NO_NSYNC
	CFLAGS += -DTY_USE_NSYNC
	CFLAGS += -Insync/public
endif

# --- Default to ncpu parallel jobs ---
NPROC := $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
MAKEFLAGS += -j$(NPROC)

# --- Auto-rebuild on config change ---
BUILD_SIG := DEBUG=$(DEBUG)|LOG=$(LOG)|NO_JIT=$(NO_JIT)|RELEASE=$(RELEASE)|TDEBUG=$(TDEBUG)|UNSAFE=$(UNSAFE)|LTO=$(LTO)|JEMALLOC=$(JEMALLOC)|TY_PROFILER=$(TY_PROFILER)|DEBUG_NAMES=$(DEBUG_NAMES)|PROFILE_TYPES=$(PROFILE_TYPES)|BOX_STATS=$(BOX_STATS)|WITHOUT_OS=$(WITHOUT_OS)|GENPROF=$(GENPROF)|USEPROF=$(USEPROF)|NO_NSYNC=$(NO_NSYNC)
BUILD_SIG_FILE := obj/.build_sig

PREV_SIG := $(shell cat $(BUILD_SIG_FILE) 2>/dev/null)

ifneq ($(BUILD_SIG),$(PREV_SIG))
$(shell rm -f obj/*.o obj/tyls/*.o obj/typrof/*.o obj/ty-main.o obj/tyls-main.o obj/typrof-main.o obj/*.d obj/tyls/*.d obj/typrof/*.d $(PROG) tyls typrof)
$(shell mkdir -p obj obj/tyls obj/typrof)
$(shell echo '$(BUILD_SIG)' > $(BUILD_SIG_FILE))
endif

# DynASM configuration
LUAJIT := luajit
DYNASM := $(LUAJIT) dynasm/dynasm.lua

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
TYPROF_OBJECTS := $(patsubst src/%.c,obj/typrof/%.o,$(SOURCES))
TYPROF_CAPSTONE_CFLAGS = $(shell pkg-config --cflags capstone 2>/dev/null)
TYPROF_CAPSTONE_LIBS = $(shell pkg-config --libs capstone 2>/dev/null)
EXTERNAL := libco/libco.o dtoa/dtoa.o libmd/libmd.a
ifndef NO_NSYNC
	EXTERNAL += nsync/out/libnsync.a
endif
ASSEMBLY := $(patsubst %.c,%.s,$(SOURCES))
.DEFAULT_GOAL := all
DEPFILES := $(OBJECTS:.o=.d) $(TYLS_OBJECTS:.o=.d) $(TYPROF_OBJECTS:.o=.d) \
            obj/ty-main.d obj/tyls-main.d obj/typrof-main.d

-include $(DEPFILES)

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
obj/typrof/token.o: include/keywords.h

# jit.c depends on the generated DynASM header
obj/jit.o: $(JIT_HDR)
obj/tyls/jit.o: $(JIT_HDR)
obj/typrof/jit.o: $(JIT_HDR)

ty: obj/ty-main.o $(OBJECTS) $(EXTERNAL)
	@echo cc $@
	@$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

tyls: obj/tyls-main.o $(TYLS_OBJECTS) $(EXTERNAL)
	@echo cc $@
	@$(CC) $(CFLAGS) -DTY_LS -o $@ $^ $(LDFLAGS)

typrof: obj/typrof-main.o $(TYPROF_OBJECTS) $(EXTERNAL)
	@echo cc $@
	@$(CC) $(CFLAGS) -DTY_PROFILER -DTY_HAVE_CAPSTONE -o $@ $^ $(LDFLAGS) $(TYPROF_CAPSTONE_LIBS)

obj/ty-main.o: ty.c
	@echo cc $<
	@$(CC) $(CFLAGS) -MMD -MP -MF obj/ty-main.d -c -o $@ $<

obj/tyls-main.o: tyls.c
	@echo cc $<
	@$(CC) $(CFLAGS) -DTY_LS -MMD -MP -MF obj/tyls-main.d -c -o $@ $<

obj/typrof-main.o: ty.c
	@echo cc $<
	@$(CC) $(CFLAGS) -DTY_PROFILER -MMD -MP -MF obj/typrof-main.d -c -o $@ $<

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
	@$(CC) $(CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ -DFILENAME=$(patsubst src/%.c,%,$<) $<

obj/tyls/%.o: src/%.c
	@echo cc $<
	@$(CC) $(CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ -DTY_LS -DFILENAME=$(patsubst src/%.c,%,$<) $<

obj/typrof/%.o: src/%.c
	@echo cc $<
	@$(CC) $(CFLAGS) $(TYPROF_CAPSTONE_CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ -DTY_PROFILER -DTY_HAVE_CAPSTONE -DFILENAME=$(patsubst src/%.c,%,$<) $<


clean:
	rm -rf $(PROG) *.gcda $(OBJECTS) $(TYLS_OBJECTS) $(TYPROF_OBJECTS) libco/libco.o dtoa/dtoa.o include/keywords.h $(BUILD_SIG_FILE) $(DEPFILES) obj/ty-main.o obj/tyls-main.o obj/typrof-main.o

test:
	./ty test.ty

install: $(PROG)
	sudo install -m755 -s $(PROG) $(DESTDIR)$(PREFIX)$(bindir)
	install -d $(HOME)/.ty
	install -m644 lib/* $(HOME)/.ty

based: $(SOURCES)
	cat $^ | gcc-13 $(CFLAGS) -c -x c -o $@ -
