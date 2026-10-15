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

TEST_ARGS ?=

PROG := ty
PREFIX ?= /usr/local

bindir := /bin

ifndef LOG
	CFLAGS += -DTY_NO_LOG
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

CFLAGS += -Insync/public

# --- Default to ncpu parallel jobs ---
NPROC := $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
MAKEFLAGS += -j$(NPROC)

# --- Auto-rebuild on config change ---
BUILD_SIG := DEBUG=$(DEBUG)|LOG=$(LOG)|RELEASE=$(RELEASE)|TDEBUG=$(TDEBUG)|UNSAFE=$(UNSAFE)|LTO=$(LTO)|JEMALLOC=$(JEMALLOC)|TY_PROFILER=$(TY_PROFILER)|DEBUG_NAMES=$(DEBUG_NAMES)|PROFILE_TYPES=$(PROFILE_TYPES)|WITHOUT_OS=$(WITHOUT_OS)|GENPROF=$(GENPROF)|USEPROF=$(USEPROF)
BUILD_SIG_FILE := obj/.build_sig

PREV_SIG := $(shell cat $(BUILD_SIG_FILE) 2>/dev/null)

ifneq ($(BUILD_SIG),$(PREV_SIG))
$(shell rm -rf obj)
$(shell mkdir -p obj)
$(shell echo '$(BUILD_SIG)' > $(BUILD_SIG_FILE))
endif

$(shell mkdir -p obj/jit/lir obj/tyls/jit/lir obj/typrof/jit/lir obj/tytest/jit/lir)

# DynASM configuration
LUAJIT := luajit
DYNASM := $(LUAJIT) dynasm/dynasm.lua

ifeq ($(shell uname -m),arm64)
	LIR_DASC := src/jit/lir/arm64.dasc
	LIR_HDR  := src/jit/lir/arm64.h
else
	LIR_DASC := src/jit/lir/x64.dasc
	LIR_HDR  := src/jit/lir/x64.h
endif

SOURCES := $(wildcard src/*.c src/jit/*.c src/jit/lir/*.c)
OBJECTS := $(patsubst src/%.c,obj/%.o,$(SOURCES))
TYLS_OBJECTS := $(patsubst src/%.c,obj/tyls/%.o,$(SOURCES))
TYPROF_OBJECTS := $(patsubst src/%.c,obj/typrof/%.o,$(SOURCES))
TYTEST_OBJECTS := $(patsubst src/%.c,obj/tytest/%.o,$(SOURCES))
EXTERNAL := obj/libco.o obj/dtoa.o libmd/libmd.a nsync/out/libnsync.a
ASSEMBLY := $(patsubst %.c,%.s,$(SOURCES))
.DEFAULT_GOAL := all
.PHONY: all clean test test-types2 test-lir test-jitmem install freebsd-plist
DEPFILES := $(OBJECTS:.o=.d) $(TYLS_OBJECTS:.o=.d) $(TYPROF_OBJECTS:.o=.d) \
            $(TYTEST_OBJECTS:.o=.d) \
            obj/ty-main.d obj/tyls-main.d obj/typrof-main.d obj/tytest-main.d \
            obj/libco.d obj/dtoa.d

-include $(DEPFILES)

all: $(PROG)

ifneq ($(LIR_HDR),)
$(LIR_HDR): $(LIR_DASC) dynasm/dasm_arm64.lua dynasm/dasm_x86.lua dynasm/dynasm.lua
	@echo dynasm $<
	@$(DYNASM) -o $@ $<
endif

include/keywords.h: src/keywords.gperf
	@echo gperf $<
	@gperf $< > $@

include/optokens.h: src/optokens.gperf
	@echo gperf $<
	@gperf $< > $@

include/syscall_names.h: scripts/getsyscalls.sh
	@echo sh $<
	@sh $< > $@

GEN_DIR     := include/gen
GEN_SOURCES := src/functions.c src/ffi.c src/sqlite.c src/screen.c src/jit/mod.c
GEN_METHODS := src/str.c src/array.c src/dict.c src/blob.c src/heap.c src/queue.c src/set.c src/shared_queue.c
GEN_HEADERS := $(GEN_DIR)/builtin_decls.h $(GEN_DIR)/builtin_table.h $(GEN_DIR)/builtin_method_src.h

tools/tybi: tools/tybi.c
	@echo cc $@
	@$(CC) -std=c11 -O1 -o $@ $<

$(GEN_DIR)/.stamp: tools/tybi $(GEN_SOURCES) $(GEN_METHODS)
	@echo tybi $(GEN_SOURCES) -m $(GEN_METHODS)
	@mkdir -p $(GEN_DIR)
	@tools/tybi $(GEN_DIR) $(GEN_SOURCES) -m $(GEN_METHODS)
	@touch $@

$(GEN_HEADERS): $(GEN_DIR)/.stamp
	@test -f $@

$(OBJECTS) $(TYLS_OBJECTS) $(TYPROF_OBJECTS) $(TYTEST_OBJECTS): | $(GEN_HEADERS)
obj/ty-main.o obj/tyls-main.o obj/typrof-main.o obj/tytest-main.o: | $(GEN_HEADERS)

obj/token.o: include/keywords.h include/optokens.h
obj/functions.o obj/tyls/functions.o obj/typrof/functions.o obj/tytest/functions.o: include/syscall_names.h
obj/tyls/token.o: include/keywords.h include/optokens.h
obj/typrof/token.o: include/keywords.h include/optokens.h
obj/tytest/token.o: include/keywords.h include/optokens.h

obj/jit/lir/emit.o obj/tyls/jit/lir/emit.o obj/typrof/jit/lir/emit.o obj/tytest/jit/lir/emit.o: $(LIR_HDR)

ty: obj/ty-main.o $(OBJECTS) $(EXTERNAL)
	@echo cc $@
	@$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

tyls: obj/tyls-main.o $(TYLS_OBJECTS) $(EXTERNAL)
	@echo cc $@
	@$(CC) $(CFLAGS) -DTY_LS -o $@ $^ $(LDFLAGS)

typrof: obj/typrof-main.o $(TYPROF_OBJECTS) $(EXTERNAL)
	@echo cc $@
	@$(CC) $(CFLAGS) -DTY_PROFILER -o $@ $^ $(LDFLAGS)

tytest: obj/tytest-main.o $(TYTEST_OBJECTS) $(EXTERNAL)
	@echo cc $@
	@$(CC) $(CFLAGS) -DTY_TEST -o $@ $^ $(LDFLAGS)

obj/ty-main.o: ty.c
	@echo cc $<
	@$(CC) $(CFLAGS) -MMD -MP -MF obj/ty-main.d -c -o $@ $<

obj/tyls-main.o: tyls.c
	@echo cc $<
	@$(CC) $(CFLAGS) -DTY_LS -MMD -MP -MF obj/tyls-main.d -c -o $@ $<

obj/typrof-main.o: ty.c
	@echo cc $<
	@$(CC) $(CFLAGS) -DTY_PROFILER -MMD -MP -MF obj/typrof-main.d -c -o $@ $<

obj/tytest-main.o: ty.c
	@echo cc $<
	@$(CC) $(CFLAGS) -DTY_TEST -MMD -MP -MF obj/tytest-main.d -c -o $@ $<

asm: $(ASSEMBLY)

%.s: src/%.c
	@echo cc $<
	$(CC) $(CFLAGS) -S -o asm/$@ -DFILENAME=$(patsubst %.c,%,$<) $<

obj/libco.o: libco/libco.c
	$(CC) $(CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ -DLIBCO_MP $<

obj/dtoa.o: dtoa/SwiftDtoa.c
	$(CC) $(CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ $<

nsync/out/libnsync.a: nsync/CMakeLists.txt
	@echo cmake nsync
	@rm -rf nsync/out
	@CC="$(CC)" cmake -S nsync -B nsync/out -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_FLAGS=-w >/dev/null
	@MAKEFLAGS= cmake --build nsync/out --target nsync --parallel $(NPROC) >/dev/null

obj/%.o: src/%.c
	@echo cc $<
	@$(CC) $(CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ -DFILENAME=$(patsubst src/%.c,%,$<) $<

obj/tyls/%.o: src/%.c
	@echo cc $<
	@$(CC) $(CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ -DTY_LS -DFILENAME=$(patsubst src/%.c,%,$<) $<

obj/typrof/%.o: src/%.c
	@echo cc $<
	@$(CC) $(CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ -DTY_PROFILER -DFILENAME=$(patsubst src/%.c,%,$<) $<

obj/tytest:
	@mkdir -p $@

$(TYTEST_OBJECTS) obj/tytest-main.o: | obj/tytest

obj/tytest/%.o: src/%.c
	@echo cc $<
	@$(CC) $(CFLAGS) -MMD -MP -MF $(@:.o=.d) -c -o $@ -DTY_TEST -DFILENAME=$(patsubst src/%.c,%,$<) $<


clean:
	rm -rf $(PROG) *.gcda $(OBJECTS) $(TYLS_OBJECTS) $(TYPROF_OBJECTS) $(TYTEST_OBJECTS) obj/libco.o obj/dtoa.o include/keywords.h include/optokens.h $(GEN_DIR) tools/tybi $(BUILD_SIG_FILE) $(DEPFILES) obj/ty-main.o obj/tyls-main.o obj/typrof-main.o obj/tytest-main.o obj/types2-core-test obj/lir-core-test obj/lir-interp-test obj/lir-ra-test obj/lir-native-test obj/lir-entry-test obj/jitmem-test tytest

test: ty tyls tytest test-types2 test-lir test-jitmem test-jit
	TY_TEST_NATIVE=1 ./ty --test tests/runner/smoke.ty
	./ty --test tests --strict $(TEST_ARGS)

test-jit: ty tytest
	TY_JIT_EAGER=1 ./ty --test tests --strict $(TEST_ARGS)
	TY_JIT_EAGER=2 TY_JIT_TIER=3 ./ty --test tests --strict $(TEST_ARGS)

test-types2: obj/types2-core-test
	./obj/types2-core-test

obj/types2-core-test: tests/types2_core.c src/types2_core.c src/panic.c include/types2_core.h
	@echo cc $@
	@$(CC) $(CFLAGS) -o $@ tests/types2_core.c src/types2_core.c src/panic.c $(LDFLAGS)

LIR_TESTS  := core interp ra native entry
LIR_HEADER := include/jit/lir.h tests/jit/lir/test.h tests/jit/lir/scalar.h
LIR_CORE   := $(addprefix obj/jit/lir/,lir.o check.o cfg.o wire.o entry.o) obj/panic.o
LIR_NATIVE := $(addprefix obj/jit/lir/,interp.o ra.o norm.o emit.o finish.o) obj/jit/mem.o nsync/out/libnsync.a

define LINK_TEST
	@echo cc $@
	@$(CC) $(CFLAGS) -o $@ $< $(filter %.o %.a,$^) $(LDFLAGS)
endef

test-lir: $(LIR_TESTS:%=obj/lir-%-test)
	@set -e; for t in $^; do echo ./$$t; ./$$t; done

test-jitmem: obj/jitmem-test
	./obj/jitmem-test

obj/lir-%-test: tests/jit/lir/%.c $(LIR_HEADER) $(LIR_CORE)
	$(LINK_TEST)

obj/lir-interp-test: obj/jit/lir/interp.o
obj/lir-ra-test:     obj/jit/lir/ra.o
obj/lir-native-test: $(LIR_NATIVE)
obj/lir-entry-test:  $(LIR_NATIVE)

obj/jitmem-test: tests/jit/mem.c $(LIR_HEADER) obj/jit/mem.o obj/panic.o nsync/out/libnsync.a
	$(LINK_TEST)

LIB_DIRS = $(sort $(dir $(shell find lib -type f -name '*.ty')))
LIB_HOME = $(or $(XDG_DATA_HOME),$(HOME)/.local/share)/ty/lib

define install-lib-dir
	install -d $(LIB_HOME)/$(patsubst lib/%,%,$(1))
	install -m644 $(1)*.ty $(LIB_HOME)/$(patsubst lib/%,%,$(1))

endef

install: $(PROG) tytest
	sudo install -m755 -s $(PROG) tytest $(DESTDIR)$(PREFIX)$(bindir)
	$(foreach d,$(LIB_DIRS),$(call install-lib-dir,$(d)))

freebsd-plist:
	{ printf 'bin/ty\nbin/tyls\nbin/tytest\n'; \
	  git ls-files 'lib/*.ty' \
	  | sed 's|^lib/|%%TYMODDIR%%/|' \
	  | LC_ALL=C sort; } > freebsd/pkg-plist

based: $(SOURCES)
	cat $^ | gcc-13 $(CFLAGS) -c -x c -o $@ -
