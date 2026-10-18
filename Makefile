MODE := dev
ifdef DEBUG
	MODE := debug
endif
ifdef RELEASE
	MODE := release
endif

BUILD      := _build/$(MODE)
TOOLS      := _build/tools.mk
VCPKG      := _vcpkg/vcpkg
VCPKG_REPO := https://github.com/microsoft/vcpkg.git
VCPKG_REV  := 5d57f5a0a5469a23e005fc79a7c1814ab4fc967e
LOG_OPT    := $(if $(LOG),ON,OFF)
TEST_ARGS  ?=

LEGACY := obj tools/tybi include/gen include/keywords.h include/optokens.h \
          include/syscall_names.h include/ioctl_constants.h \
          include/errno_constants.h nsync/out

.DEFAULT_GOAL := all
.PHONY: all test clean freebsd-plist FORCE

ifneq ($(filter-out clean freebsd-plist,$(or $(MAKECMDGOALS),all)),)
-include $(TOOLS)
endif

CTEST := $(dir $(CMAKE))ctest

all: $(BUILD)/build.ninja
	@$(NINJA) -C $(BUILD) ty
	@cp $(BUILD)/ty ty.tmp && mv ty.tmp ty
	@ln -sf $(BUILD)/compile_commands.json compile_commands.json

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

$(BUILD)/.config: FORCE
	@mkdir -p $(@D)
	@echo 'LOG=$(LOG_OPT)' | cmp -s - $@ || echo 'LOG=$(LOG_OPT)' > $@

$(BUILD)/build.ninja: $(BUILD)/.config | $(TOOLS)
	$(CMAKE) --preset $(MODE) -DCMAKE_MAKE_PROGRAM=$(NINJA) -DTY_LOG=$(LOG_OPT)
	@touch $@

clean:
	rm -rf _build/dev _build/debug _build/release ty compile_commands.json $(LEGACY)

freebsd-plist:
	{ printf 'bin/ty\n'; \
	  git ls-files 'lib/*.ty' \
	  | sed 's|^lib/|%%TYMODDIR%%/|' \
	  | LC_ALL=C sort; } > freebsd/pkg-plist
