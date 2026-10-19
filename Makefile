MODE := dev
ifdef DEBUG
	MODE := debug
endif
ifdef RELEASE
	MODE := release
endif
ifdef OPTIMIZED
	MODE := optimized
endif

BUILD      := _build/$(MODE)
TOOLS      := _build/tools.mk
VCPKG      := _vcpkg/vcpkg
VCPKG_REPO := https://github.com/microsoft/vcpkg.git
VCPKG_REV  := 5d57f5a0a5469a23e005fc79a7c1814ab4fc967e
LOG_OPT    := $(if $(LOG),ON,OFF)
TEST_ARGS  ?=

PGO_BUILD     := _build/optimized-instrumented
PGO_RAW       := $(PGO_BUILD)/profiles
PGO_PROFDATA  := $(PGO_BUILD)/ty.profdata
LLVM_PROFDATA ?= $(shell xcrun -f llvm-profdata 2>/dev/null || command -v llvm-profdata)
LLVM_BOLT     ?= $(or $(realpath $(shell command -v llvm-bolt)),llvm-bolt)
MERGE_FDATA   ?= merge-fdata
BOLT_FLAGS    ?= -reorder-blocks=ext-tsp -reorder-functions=cdsort \
                 -split-functions -split-all-cold -split-eh -icf=1 \
                 -use-gnu-stack -dyno-stats

ifeq ($(shell uname -s),Linux)
	BOLT ?= 1
endif

OUT        := $(BUILD)/ty
CMAKE_ARGS :=
CONFIG      = $(strip LOG=$(LOG_OPT) $(CMAKE_ARGS))
ifeq ($(MODE),optimized)
	CMAKE_ARGS := -DTY_PGO_USE=$(abspath $(PGO_PROFDATA))
	ifeq ($(BOLT),1)
		CMAKE_ARGS += -DTY_BOLT=ON
		OUT        := $(BUILD)/ty.bolt
	else
		CMAKE_ARGS += -DTY_BOLT=OFF
	endif
endif

define pgo-train
-$(1) --test tests >$(2)/train.log 2>&1
-$(1) bench/richards.ty >>$(2)/train.log 2>&1
-$(1) -j bench/richards.ty >>$(2)/train.log 2>&1
endef

LEGACY := obj tools/tybi include/gen include/keywords.h include/optokens.h \
          include/syscall_names.h include/ioctl_constants.h \
          include/errno_constants.h nsync/out

.DEFAULT_GOAL := all
.PHONY: all test clean freebsd-plist FORCE
.PRECIOUS: _build/%/.config _build/%/build.ninja _build/%/ty

ifneq ($(filter-out clean freebsd-plist,$(or $(MAKECMDGOALS),all)),)
-include $(TOOLS)
endif

CTEST := $(dir $(CMAKE))ctest

all: $(OUT)
	@cp $(OUT) ty.tmp && mv ty.tmp ty
	@ln -sf $(BUILD)/compile_commands.json compile_commands.json

_build/%/ty: _build/%/build.ninja FORCE
	@$(NINJA) -C $(@D) ty

ifeq ($(MODE),optimized)
$(BUILD)/build.ninja: | $(PGO_PROFDATA)
$(BUILD)/ty: $(PGO_PROFDATA)

$(PGO_BUILD)/build.ninja: CMAKE_ARGS := -DTY_PGO_GENERATE=$(abspath $(PGO_RAW))

$(PGO_PROFDATA): $(PGO_BUILD)/ty
	rm -rf $(PGO_RAW)
	@mkdir -p $(PGO_RAW)
	$(call pgo-train,$<,$(PGO_BUILD))
	$(LLVM_PROFDATA) merge -o $@ $(PGO_RAW)
	@! test -f $(BUILD)/build.ninja || $(NINJA) -C $(BUILD) -t clean

$(BUILD)/ty.bolt: $(BUILD)/ty
	rm -rf $(BUILD)/bolt
	@mkdir -p $(BUILD)/bolt
	$(LLVM_BOLT) $< -instrument -o $(BUILD)/ty.inst \
		--instrumentation-file=$(abspath $(BUILD))/bolt/ty.fdata \
		--instrumentation-file-append-pid
	$(call pgo-train,$(BUILD)/ty.inst,$(BUILD)/bolt)
	$(MERGE_FDATA) $(BUILD)/bolt/*.fdata >$(BUILD)/ty.fdata
	$(LLVM_BOLT) $< -o $@ -data=$(BUILD)/ty.fdata $(BOLT_FLAGS)
endif

test: all
	@$(NINJA) -C $(BUILD)
	$(CTEST) --test-dir $(BUILD) --output-on-failure
	TY_TEST_NATIVE=1 ./ty --test tests/runner/smoke.ty
	./ty --test tests --strict $(TEST_ARGS)
	TY_JIT_EAGER=1 ./ty --test tests --strict $(TEST_ARGS)
	TY_JIT_EAGER=2 TY_JIT_TIER=3 ./ty --test tests --strict $(TEST_ARGS)

$(VCPKG):
	@test -d _vcpkg/.git || git init -q _vcpkg
	git -C _vcpkg fetch -q --depth 1 $(VCPKG_REPO) $(VCPKG_REV)
	@git -C _vcpkg checkout -q $(VCPKG_REV)
	_vcpkg/bootstrap-vcpkg.sh -disableMetrics

$(TOOLS): | $(VCPKG)
	@mkdir -p $(@D)
	@cmake=$$($(VCPKG) fetch cmake --x-stderr-status) \
	 && ninja=$$($(VCPKG) fetch ninja --x-stderr-status) \
	 && printf 'CMAKE := %s\nNINJA := %s\n' "$$cmake" "$$ninja" > $@

_build/%/.config: FORCE
	@mkdir -p $(@D)
	@echo '$(CONFIG)' | cmp -s - $@ || echo '$(CONFIG)' > $@

_build/%/build.ninja: _build/%/.config CMakePresets.json | $(TOOLS)
	$(CMAKE) --preset $* -DCMAKE_MAKE_PROGRAM=$(NINJA) -DTY_LOG=$(LOG_OPT) $(CMAKE_ARGS)
	@touch $@

clean:
	rm -rf _build/dev _build/debug _build/release _build/optimized $(PGO_BUILD) ty compile_commands.json $(LEGACY)

freebsd-plist:
	{ printf 'bin/ty\n'; \
	  git ls-files 'lib/*.ty' \
	  | sed 's|^lib/|%%TYMODDIR%%/|' \
	  | LC_ALL=C sort; } > freebsd/pkg-plist
