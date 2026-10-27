cmake_minimum_required(VERSION 3.21)

project(ty VERSION 0.1 LANGUAGES C)

include(cmake/VersionInfoTarget.cmake)

# ---
#   user-defined options
# ---

option(USE_SYSTEM_DEPS "Use system-installed libraries instead of vcpkg (e.g. FreeBSD ports)" OFF)
option(TY_EMBED_LIB "Embed lib/*.ty in the executable" OFF)
option(TY_LOG "Compile in debug logging" OFF)
option(TY_ASAN "Build with AddressSanitizer" OFF)
option(TY_SYSMALLOC "Route all allocation (including arenas) through the system malloc" OFF)
option(TY_NATIVE "Tune for the build machine's CPU (-mcpu=native / -march=native)" OFF)
option(TY_LTO_FULL "Use full LTO instead of ThinLTO for Release builds" OFF)
set(TY_PGO_GENERATE "" CACHE PATH "Instrument for PGO, writing raw profiles to this directory")
set(TY_PGO_USE "" CACHE FILEPATH "Optimize with this merged PGO profile (.profdata)")
option(TY_BOLT "Keep relocations in the executable so it can be post-link optimized with BOLT" OFF)
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  option(TY_USDT "Compile USDT (SystemTap/bpftrace) probes into the executables" ON)
else()
  option(TY_USDT "Compile USDT (SystemTap/bpftrace) probes into the executables" OFF)
endif()
find_program(TY_MOLD NAMES ld64.mold mold)
if(TY_MOLD)
  option(TY_USE_MOLD "Link with mold" ON)
else()
  option(TY_USE_MOLD "Link with mold" OFF)
endif()

include(CTest)

# ---
#   find 3rd-party dependencies
# ---

# defines target(s): Threads::Threads
find_package(Threads REQUIRED)

if(USE_SYSTEM_DEPS)
  # Use pkg-config / find_library for system-installed deps (FreeBSD ports, etc.)
  # Creates the same IMPORTED targets that the vcpkg CONFIG packages would.
  include(${PROJECT_SOURCE_DIR}/cmake/FindSystemDeps.cmake)
else()
  # defines target(s): unofficial::libffi::libffi
  find_package(unofficial-libffi CONFIG REQUIRED)
  # defines target(s): unofficial::sqlite3::sqlite3
  find_package(unofficial-sqlite3 CONFIG REQUIRED)
  # defines target(s): utf8proc::utf8proc
  find_package(utf8proc CONFIG REQUIRED)
  # defines target(s): PCRE2::8BIT, PCRE2::16BIT, PCRE2::32BIT, PCRE2::POSIX
  find_package(pcre2 CONFIG REQUIRED)
  # defines target(s): xxHash::xxhash
  find_package(xxHash CONFIG REQUIRED)
  # defines target(s): mimalloc, mimalloc-static
  find_package(mimalloc CONFIG REQUIRED)
  # defines target(s): nghttp2::nghttp2 (the port installs no CMake config)
  find_path(_nghttp2_inc NAMES nghttp2/nghttp2.h REQUIRED)
  find_library(_nghttp2_lib NAMES libnghttp2.a nghttp2 REQUIRED)
  add_library(nghttp2::nghttp2 STATIC IMPORTED)
  set_target_properties(nghttp2::nghttp2 PROPERTIES
    IMPORTED_LOCATION "${_nghttp2_lib}"
    INTERFACE_INCLUDE_DIRECTORIES "${_nghttp2_inc}"
    INTERFACE_COMPILE_DEFINITIONS NGHTTP2_STATICLIB
  )
  # defines target(s): llhttp::llhttp_static
  find_package(llhttp CONFIG REQUIRED)
  # defines target(s): ZLIB::ZLIB
  find_package(ZLIB REQUIRED)
  # defines target(s): zstd::libzstd
  find_package(zstd CONFIG REQUIRED)
  set_target_properties(mimalloc-static PROPERTIES
    IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
  )
endif()

# ---
#   global compiler variables
# ---

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Enable LTO for release builds so vendored libs (libco, dtoa, etc.) also participate
include(CheckIPOSupported)
check_ipo_supported(RESULT _lto_supported OUTPUT _lto_error)
if(_lto_supported AND CMAKE_BUILD_TYPE STREQUAL "Release")
  set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()

if(TY_LTO_FULL)
  if(NOT CMAKE_C_COMPILER_ID MATCHES "Clang")
    message(FATAL_ERROR "TY_LTO_FULL requires Clang")
  endif()
  set(CMAKE_C_COMPILE_OPTIONS_IPO -flto=full)
  set(CMAKE_C_LINK_OPTIONS_IPO -flto=full)
endif()

if(TY_PGO_GENERATE AND TY_PGO_USE)
  message(FATAL_ERROR "TY_PGO_GENERATE and TY_PGO_USE are mutually exclusive")
endif()

if((TY_PGO_GENERATE OR TY_PGO_USE) AND NOT CMAKE_C_COMPILER_ID MATCHES "Clang")
  message(FATAL_ERROR "PGO requires Clang")
endif()

if(TY_PGO_GENERATE)
  add_compile_options(-fprofile-generate=${TY_PGO_GENERATE} "SHELL:-mllvm -vp-counters-per-site=8")
  add_link_options(-fprofile-generate=${TY_PGO_GENERATE})
elseif(TY_PGO_USE)
  if(NOT EXISTS ${TY_PGO_USE})
    message(FATAL_ERROR "TY_PGO_USE: ${TY_PGO_USE} does not exist")
  endif()
  add_compile_options(-fprofile-use=${TY_PGO_USE} -Wno-profile-instr-unprofiled)
  add_link_options(-fprofile-use=${TY_PGO_USE})
endif()

if(TY_BOLT)
  if(NOT CMAKE_SYSTEM_NAME STREQUAL "Linux")
    message(FATAL_ERROR "TY_BOLT is only supported on Linux")
  endif()
  add_link_options(-Wl,--emit-relocs)
endif()

if(TY_NATIVE)
  if(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64|ARM64")
    add_compile_options(-mcpu=native)
  else()
    add_compile_options(-march=native)
  endif()
endif()

if(TY_ASAN)
  add_compile_options(-fsanitize=address -fno-sanitize-address-use-after-scope)
  if(CMAKE_C_COMPILER_ID STREQUAL "GNU")
    add_compile_options("SHELL:--param asan-stack=0")
  else()
    add_compile_options("SHELL:-mllvm -asan-stack=0")
  endif()
  add_link_options(-fsanitize=address)
endif()

if(TY_USE_MOLD AND TY_BOLT)
  message(STATUS "TY_BOLT: not linking with mold (llvm-bolt misparses its PLT header)")
  set(TY_USE_MOLD OFF)
endif()

if(TY_USE_MOLD)
  include(CheckLinkerFlag)
  check_linker_flag(C "-fuse-ld=mold" _mold_supported)
  if(NOT _mold_supported)
    message(FATAL_ERROR "TY_USE_MOLD: ${CMAKE_C_COMPILER} cannot link with -fuse-ld=mold")
  endif()
  add_link_options(-fuse-ld=mold)
endif()

# ---
#  generate ioctl constants
# ---

set(_autogen_dir ${PROJECT_BINARY_DIR}/GeneratedFiles)
file(MAKE_DIRECTORY ${_autogen_dir})
file(MAKE_DIRECTORY ${_autogen_dir}/include)

set(_file_ioctl_constants_h ${_autogen_dir}/include/ioctl_constants.h)
set(_gen_ioctl_script       ${PROJECT_SOURCE_DIR}/scripts/getioctls.sh)

set(_tgt_ioctlconstants_h "IoctlConstantsH")
add_library(${_tgt_ioctlconstants_h} INTERFACE)
target_include_directories(${_tgt_ioctlconstants_h}
  INTERFACE
    ${_autogen_dir}/include
)

if (WIN32)
  if (NOT EXISTS ${_file_ioctl_constants_h})
    file(TOUCH ${_file_ioctl_constants_h})
  endif()
else()
  set(_tgt_gen_ioctl_h GenerateIoctlConstantsH)
  add_custom_target(${_tgt_gen_ioctl_h}
    BYPRODUCTS
      ${_file_ioctl_constants_h}
    COMMAND # generate tmp file
      sh "${_gen_ioctl_script}" > "${_file_ioctl_constants_h}.tmp"
    COMMAND # replace existing (if different)
      ${CMAKE_COMMAND} -E copy_if_different
        "${_file_ioctl_constants_h}.tmp"
        "${_file_ioctl_constants_h}"
    COMMAND # remove tmp file
      ${CMAKE_COMMAND} -E rm "${_file_ioctl_constants_h}.tmp"
    WORKING_DIRECTORY
      "${PROJECT_SOURCE_DIR}"
    COMMENT
      "Generating ioctl_constants.h file using getioctls.sh"
    DEPENDS
      ${_gen_ioctl_script}
    VERBATIM
  )
  add_dependencies(${_tgt_ioctlconstants_h} ${_tgt_gen_ioctl_h})
endif()

# ---
#  generate errno constants
# ---

set(_autogen_dir ${PROJECT_BINARY_DIR}/GeneratedFiles)
file(MAKE_DIRECTORY ${_autogen_dir})
file(MAKE_DIRECTORY ${_autogen_dir}/include)

set(_file_errno_constants_h ${_autogen_dir}/include/errno_constants.h)
set(_gen_errno_script       ${PROJECT_SOURCE_DIR}/scripts/geterrnos.sh)
set(_file_syscall_names_h   ${_autogen_dir}/include/syscall_names.h)
set(_gen_syscall_script     ${PROJECT_SOURCE_DIR}/scripts/getsyscalls.sh)

set(_tgt_errnoconstants_h "ErrnoConstantsH")
add_library(${_tgt_errnoconstants_h} INTERFACE)
target_include_directories(${_tgt_errnoconstants_h}
  INTERFACE
    ${_autogen_dir}/include
)

if (WIN32)
  if (NOT EXISTS ${_file_errno_constants_h})
    file(TOUCH ${_file_errno_constants_h})
  endif()
  if (NOT EXISTS ${_file_syscall_names_h})
    file(TOUCH ${_file_syscall_names_h})
  endif()
else()
  set(_tgt_gen_errno_h GenerateErrnoConstantsH)
  add_custom_target(${_tgt_gen_errno_h}
    BYPRODUCTS
      ${_file_errno_constants_h}
      ${_file_syscall_names_h}
    COMMAND # generate tmp file
      sh "${_gen_errno_script}" > "${_file_errno_constants_h}.tmp"
    COMMAND # replace existing (if different)
      ${CMAKE_COMMAND} -E copy_if_different
        "${_file_errno_constants_h}.tmp"
        "${_file_errno_constants_h}"
    COMMAND # remove tmp file
      ${CMAKE_COMMAND} -E rm "${_file_errno_constants_h}.tmp"
    COMMAND
      sh "${_gen_syscall_script}" > "${_file_syscall_names_h}.tmp"
    COMMAND
      ${CMAKE_COMMAND} -E copy_if_different
        "${_file_syscall_names_h}.tmp"
        "${_file_syscall_names_h}"
    COMMAND
      ${CMAKE_COMMAND} -E rm "${_file_syscall_names_h}.tmp"
    WORKING_DIRECTORY
      "${PROJECT_SOURCE_DIR}"
    COMMENT
      "Generating errno_constants.h file using geterrnos.sh"
    DEPENDS
      ${_gen_errno_script}
      ${_gen_syscall_script}
    VERBATIM
  )
  add_dependencies(${_tgt_errnoconstants_h} ${_tgt_gen_errno_h})
endif()

# ---
#  generate keyword perfect hash
# ---

set(_file_keywords_h  ${_autogen_dir}/include/keywords.h)
set(_gperf_input      ${PROJECT_SOURCE_DIR}/src/keywords.gperf)

find_program(GPERF gperf)
if(GPERF)
  add_custom_command(
    OUTPUT
      ${_file_keywords_h}
    COMMAND
      ${GPERF} "${_gperf_input}" > "${_file_keywords_h}.tmp"
    COMMAND
      ${CMAKE_COMMAND} -E copy_if_different
        "${_file_keywords_h}.tmp"
        "${_file_keywords_h}"
    COMMAND
      ${CMAKE_COMMAND} -E rm "${_file_keywords_h}.tmp"
    DEPENDS
      ${_gperf_input}
    COMMENT
      "Generating keywords.h from keywords.gperf"
    VERBATIM
  )
  add_custom_target(GenerateKeywordsH DEPENDS ${_file_keywords_h})
  add_dependencies(${_tgt_ioctlconstants_h} GenerateKeywordsH)
else()
  message(WARNING "gperf not found -- keywords.h will not be regenerated")
endif()

set(_file_optokens_h ${_autogen_dir}/include/optokens.h)
set(_gperf_optokens  ${PROJECT_SOURCE_DIR}/src/optokens.gperf)

if(GPERF)
  add_custom_command(
    OUTPUT
      ${_file_optokens_h}
    COMMAND
      ${GPERF} "${_gperf_optokens}" > "${_file_optokens_h}.tmp"
    COMMAND
      ${CMAKE_COMMAND} -E copy_if_different
        "${_file_optokens_h}.tmp"
        "${_file_optokens_h}"
    COMMAND
      ${CMAKE_COMMAND} -E rm "${_file_optokens_h}.tmp"
    DEPENDS
      ${_gperf_optokens}
    COMMENT
      "Generating optokens.h from optokens.gperf"
    VERBATIM
  )
  add_custom_target(GenerateOptokensH DEPENDS ${_file_optokens_h})
  add_dependencies(${_tgt_ioctlconstants_h} GenerateOptokensH)
else()
  message(WARNING "gperf not found -- optokens.h will not be regenerated")
endif()

# ---
#  generate builtin function declarations/table
# ---

add_executable(tybi)
target_sources(tybi PRIVATE tools/tybi.c)
set_target_properties(tybi PROPERTIES C_STANDARD 11)
if(TY_ASAN)
  target_compile_options(tybi PRIVATE -fno-sanitize=all)
  target_link_options(tybi PRIVATE -fno-sanitize=all)
endif()

set(_gen_builtins_dir ${_autogen_dir}/include/gen)
set(_gen_builtins_sources
  src/functions.c
  src/ffi.c
  src/sqlite.c
  src/http/io.c
  src/http/loop.c
  src/http/h1.c
  src/http/h2.c
  src/http/ws.c
  src/http/xch.c
  src/http/msg.c
  src/http/client.c
  src/codec.c
  src/ssl.c
  src/screen.c
  src/jit/mod.c
  src/syntax.c
)
set(_gen_builtins_methods
  src/str.c
  src/array.c
  src/dict.c
  src/blob.c
  src/heap.c
  src/queue.c
  src/set.c
  src/shared_queue.c
)
set(_gen_builtins_headers
  ${_gen_builtins_dir}/builtin_decls.h
  ${_gen_builtins_dir}/builtin_table.h
  ${_gen_builtins_dir}/builtin_method_src.h
)

add_custom_command(
  OUTPUT
    ${_gen_builtins_headers}
  COMMAND
    ${CMAKE_COMMAND} -E make_directory "${_gen_builtins_dir}"
  COMMAND
    $<TARGET_FILE:tybi> "${_gen_builtins_dir}" ${_gen_builtins_sources} -m ${_gen_builtins_methods}
  DEPENDS
    tybi
    ${_gen_builtins_sources}
    ${_gen_builtins_methods}
  WORKING_DIRECTORY
    "${PROJECT_SOURCE_DIR}"
  COMMENT
    "Generating builtin headers with tybi"
  VERBATIM
)
add_custom_target(GenerateBuiltinsH DEPENDS ${_gen_builtins_headers})
add_dependencies(${_tgt_ioctlconstants_h} GenerateBuiltinsH)

# ---
#  target: libco
# ---
add_library(libco)
target_sources(libco PRIVATE libco/libco.c)
target_compile_definitions(libco PRIVATE LIBCO_MP)

# ---
#  target: dtoa
# ---
add_library(dtoa)
target_sources(dtoa PRIVATE dtoa/SwiftDtoa.c)

# ---
#  target: libmd::md
# ---
add_subdirectory(libmd)
# libmd uses C_VISIBILITY_PRESET hidden which breaks ThinLTO symbol resolution
set_target_properties(md PROPERTIES INTERPROCEDURAL_OPTIMIZATION FALSE)

# ---
#  target: nsync
# ---
add_subdirectory(nsync)

# ---
#  target: unibilium
# ---
add_subdirectory(unibilium)

# ---
#  DynASM JIT code generation
# ---

add_executable(minilua dynasm/minilua.c)
target_compile_options(minilua PRIVATE $<$<NOT:$<C_COMPILER_ID:MSVC>>:-w;-fno-sanitize=all>)
target_link_libraries(minilua PRIVATE $<$<NOT:$<BOOL:${WIN32}>>:m>)
set_target_properties(minilua PROPERTIES INTERPROCEDURAL_OPTIMIZATION OFF)
if(TY_ASAN)
  target_link_options(minilua PRIVATE -fno-sanitize=all)
endif()

if(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64|ARM64")
  set(_lir_dasc ${PROJECT_SOURCE_DIR}/src/jit/lir/arm64.dasc)
else()
  set(_lir_dasc ${PROJECT_SOURCE_DIR}/src/jit/lir/x64.dasc)
endif()
set(_lir_hdr ${_autogen_dir}/include/lir_dasm.h)

add_custom_command(
  OUTPUT ${_lir_hdr}
  COMMAND $<TARGET_FILE:minilua> ${PROJECT_SOURCE_DIR}/dynasm/dynasm.lua
    -o ${_lir_hdr} ${_lir_dasc}
  DEPENDS minilua ${_lir_dasc} ${PROJECT_SOURCE_DIR}/dynasm/dasm_x86.lua dynasm/dasm_arm64.lua dynasm/dynasm.lua
  VERBATIM
)
add_custom_target(GenerateLirHeader DEPENDS ${_lir_hdr})

# ---
#  target: ty
# ---

set(_lir_core
  src/jit/lir/lir.c
  src/jit/lir/check.c
  src/jit/lir/cfg.c
  src/jit/lir/wire.c
  src/jit/lir/entry.c
  src/panic.c
  src/stbsp.c
)

set(_lir_native
  src/jit/lir/interp.c
  src/jit/lir/ra.c
  src/jit/lir/norm.c
  src/jit/lir/hoist.c
  src/jit/lir/opt.c
  src/jit/lir/emit.c
  src/jit/lir/finish.c
  src/jit/mem.c
)

set(_src_files
  src/alloc.c
  src/array.c
  src/ast.c
  src/blob.c
  src/bundle.c
  src/chan.c
  src/class.c
  src/compiler.c
  src/diag.c
  src/embed.c
  src/queue.c
  src/debug.c
  src/dict.c
  src/dirs.c
  src/set.c
  src/heap.c
  src/ffi.c
  src/functions.c
  src/gc.c
  src/highlight.c
  src/intern.c
  src/itable.c
  src/inline.c
  src/jit/jit.c
  src/jit/lower.c
  src/jit/mod.c
  ${_lir_core}
  ${_lir_native}
  src/json.c
  src/lex.c
  src/source.c
  src/ls.c
  src/mod.c
  src/object.c
  src/operators.c
  src/panic.c
  src/parse.c
  src/qcache.c
  src/vmem.c
  src/scope.c
  src/screen.c
  src/shared_queue.c
  src/spawn.c
  src/sqlite.c
  src/http/io.c
  src/http/loop.c
  src/http/h1.c
  src/http/h2.c
  src/http/ws.c
  src/http/xch.c
  src/http/msg.c
  src/http/client.c
  src/codec.c
  src/ssl.c
  src/str.c
  src/syntax.c
  src/table.c
  src/tags.c
  src/title.c
  src/token.c
  src/types2.c
  src/types2_core.c
  src/util.c
  src/value.c
  src/vm.c
  src/prof.c
  src/width.c
)

set_source_files_properties(src/vm.c PROPERTIES COMPILE_OPTIONS -U_FORTIFY_SOURCE)

if(APPLE)
  list(APPEND _src_files src/prof/darwin.c)
else()
  list(APPEND _src_files src/prof/linux.c)
endif()

set(_tgt_ty_interface "${PROJECT_NAME}_Objects")
add_library(${_tgt_ty_interface} INTERFACE)

if(TY_USDT)
  include(CheckIncludeFile)
  check_include_file(sys/sdt.h TY_HAVE_SYS_SDT_H)
  if(NOT TY_HAVE_SYS_SDT_H)
    message(WARNING "TY_USDT=ON but <sys/sdt.h> is missing (install systemtap-sdt-dev / systemtap-sdt-devel); building without probes")
  endif()
  target_compile_definitions(${_tgt_ty_interface} INTERFACE TY_USDT)
endif()

set(_tgt_ty_interface_version_info "${_tgt_ty_interface}_VersionInfo")
if(EXISTS "${PROJECT_SOURCE_DIR}/.git")
  set(_git_work_tree_arg GIT_WORK_TREE ${PROJECT_SOURCE_DIR})
  target_compile_definitions(${_tgt_ty_interface} INTERFACE TY_HAVE_GIT_STATUS)
else()
  set(_git_work_tree_arg)
  string(TIMESTAMP _ty_build_date "%a %b %d %H:%M:%S %Y %z")
  target_compile_definitions(
    ${_tgt_ty_interface}
    INTERFACE
      TY_BUILD_DATE="${_ty_build_date}"
  )
endif()
add_version_info_target(NAME ${_tgt_ty_interface_version_info}
  ${_git_work_tree_arg}
  LANGUAGE C
)

target_compile_options(${_tgt_ty_interface}
  INTERFACE
    $<$<C_COMPILER_ID:GNU>:
      -Wall
      -Wno-switch
      -Wno-unused-value
      -Wno-unused-function
      -Wno-multichar
      -Wno-trigraphs
      -pipe
    >
    $<$<C_COMPILER_ID:AppleClang>:
      -Wall
      -Wno-class-varargs
      -Wno-switch
      -Wno-string-plus-int
      -Wno-multichar
      -Wno-trigraphs
      -Wno-sign-compare
      -Wno-sign-conversion
      -Wno-padded
      -Wno-shadow
      -Wno-shorten-64-to-32
      -Wno-cast-qual
      -Wno-declaration-after-statement
      -ferror-limit=3
    >
    $<$<C_COMPILER_ID:Clang>:
      -Wall
      -Wno-class-varargs
      -Wno-switch
      -Wno-string-plus-int
      -Wno-multichar
      -Wno-trigraphs
      -Wno-sign-compare
      -Wno-sign-conversion
      -Wno-padded
      -Wno-shadow
      -Wno-shorten-64-to-32
      -Wno-cast-qual
      -Wno-declaration-after-statement
    >
    $<$<C_COMPILER_ID:MSVC>:
      /W4
      /we4013 # undefined function, assuming extern returning int
    >
)

target_sources(${_tgt_ty_interface}
  INTERFACE
    ${_src_files}
)

if(BUILD_TESTING)
  set(_lir_tests core interp ra)
  if(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64|ARM64|x86_64|amd64|AMD64")
    list(APPEND _lir_tests native entry)
  endif()
  foreach(_lir_test IN LISTS _lir_tests)
    add_executable(lir-${_lir_test}-test tests/jit/lir/${_lir_test}.c ${_lir_core})
    target_include_directories(lir-${_lir_test}-test PRIVATE include libco nsync/public ${_autogen_dir}/include)
    target_compile_definitions(lir-${_lir_test}-test PRIVATE PCRE2_CODE_UNIT_WIDTH=8 _GNU_SOURCE)
    target_compile_options(lir-${_lir_test}-test PRIVATE
      $<$<C_COMPILER_ID:GNU,Clang,AppleClang>:
        -Wall
        -Wextra
        -Wno-sign-compare
        -Wno-unused-parameter
        -Wno-unused-function
      >
    )
    target_link_libraries(lir-${_lir_test}-test PRIVATE
      unofficial::libffi::libffi PCRE2::8BIT Threads::Threads
      $<$<NOT:$<BOOL:${WIN32}>>:m>
    )
    add_test(NAME lir-${_lir_test} COMMAND lir-${_lir_test}-test)
  endforeach()
  target_sources(lir-interp-test PRIVATE src/jit/lir/interp.c)
  target_sources(lir-ra-test PRIVATE src/jit/lir/ra.c)
  foreach(_lir_test IN ITEMS native entry)
    if(TARGET lir-${_lir_test}-test)
      target_sources(lir-${_lir_test}-test PRIVATE ${_lir_native})
      target_link_libraries(lir-${_lir_test}-test PRIVATE nsync)
      if(TARGET GenerateLirHeader)
        add_dependencies(lir-${_lir_test}-test GenerateLirHeader)
      endif()
    endif()
  endforeach()
  add_executable(jitmem-test tests/jit/mem.c src/jit/mem.c src/panic.c src/stbsp.c)
  target_include_directories(jitmem-test PRIVATE include libco nsync/public)
  target_compile_definitions(jitmem-test PRIVATE PCRE2_CODE_UNIT_WIDTH=8 _GNU_SOURCE)
  target_link_libraries(jitmem-test PRIVATE nsync PCRE2::8BIT Threads::Threads)
  add_test(NAME jitmem COMMAND jitmem-test)
  add_executable(types2-core-test tests/types2_core.c src/types2_core.c src/panic.c)
  target_include_directories(types2-core-test PRIVATE include libco nsync/public)
  target_compile_definitions(types2-core-test PRIVATE PCRE2_CODE_UNIT_WIDTH=8 _GNU_SOURCE)
  target_link_libraries(types2-core-test PRIVATE
    unofficial::libffi::libffi PCRE2::8BIT xxHash::xxhash Threads::Threads
    $<$<NOT:$<BOOL:${WIN32}>>:m>
  )
  add_test(NAME types2-core COMMAND types2-core-test)
endif()

set(_tgt_ty_link "${PROJECT_NAME}_Link")
add_library(${_tgt_ty_link} INTERFACE)

target_link_libraries(${_tgt_ty_link}
  INTERFACE
    ${_tgt_ty_interface_version_info}
    ${_tgt_ioctlconstants_h}
    ${_tgt_errnoconstants_h}
    Threads::Threads # pthreads (or equivalent)
    libco
    $<$<NOT:$<OR:$<CONFIG:Debug>,$<BOOL:${TY_SYSMALLOC}>>>:mimalloc-static>
    xxHash::xxhash
    utf8proc::utf8proc
    PCRE2::8BIT
    unofficial::libffi::libffi
    libmd::md
    dtoa
    unofficial::sqlite3::sqlite3
    nghttp2::nghttp2
    llhttp::llhttp_static
    ZLIB::ZLIB
    zstd::libzstd
    $<$<NOT:$<BOOL:${WIN32}>>:${CMAKE_DL_LIBS}>
    $<$<NOT:$<BOOL:${WIN32}>>:m>
    $<$<BOOL:${WIN32}>:ws2_32> # winsock2
    $<$<BOOL:${WIN32}>:Shlwapi.lib>
    $<$<BOOL:${WIN32}>:shell32>
)

target_link_libraries(${_tgt_ty_link} INTERFACE nsync)

if(BSD OR CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_link_libraries(${_tgt_ty_link} INTERFACE util)
endif()

if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_link_options(${_tgt_ty_link} INTERFACE -Wl,--as-needed)
endif()

if(APPLE)
  target_link_libraries(${_tgt_ty_link} INTERFACE
    -Wl,-force_load,$<TARGET_FILE:unibilium>
  )
  add_dependencies(${_tgt_ty_link} unibilium)
  target_link_options(${_tgt_ty_link} INTERFACE -Wl,-export_dynamic)
else()
  target_link_libraries(${_tgt_ty_link} INTERFACE
    -Wl,--whole-archive unibilium -Wl,--no-whole-archive
  )
  target_link_options(${_tgt_ty_link} INTERFACE
    -rdynamic
    -Wl,--exclude-libs,libffi.a:libmimalloc.a:libpcre2-8.a:libsqlite3.a:libnghttp2.a:libllhttp.a:libz.a:libzstd.a:libutf8proc.a:libxxhash.a:libdtoa.a:liblibco.a:libmd.a:libnsync.a
  )
endif()

target_link_libraries(${_tgt_ty_interface} INTERFACE ${_tgt_ty_link})

if(TY_EMBED_LIB)
  add_executable(tyembed)
  target_sources(tyembed PRIVATE tools/tyembed.c)
  set_target_properties(tyembed PROPERTIES C_STANDARD 11)

  file(GLOB_RECURSE _embed_lib_files
    RELATIVE ${PROJECT_SOURCE_DIR}/lib
    CONFIGURE_DEPENDS
    ${PROJECT_SOURCE_DIR}/lib/*.ty
  )
  list(TRANSFORM _embed_lib_files
    PREPEND ${PROJECT_SOURCE_DIR}/lib/
    OUTPUT_VARIABLE _embed_lib_paths
  )

  set(_file_embedded_lib_c ${_autogen_dir}/embedded_lib.c)
  add_custom_command(
    OUTPUT
      ${_file_embedded_lib_c}
    COMMAND
      $<TARGET_FILE:tyembed> ${_file_embedded_lib_c} ${PROJECT_SOURCE_DIR}/lib
        ${_embed_lib_files}
    DEPENDS
      tyembed
      ${_embed_lib_paths}
    COMMENT
      "Embedding lib/*.ty"
    VERBATIM
  )

  add_library(ty_EmbeddedLib STATIC ${_file_embedded_lib_c})
  set_target_properties(ty_EmbeddedLib PROPERTIES INTERPROCEDURAL_OPTIMIZATION OFF)

  target_link_libraries(${_tgt_ty_link} INTERFACE ty_EmbeddedLib)
  target_compile_definitions(${_tgt_ty_interface} INTERFACE TY_EMBED_LIB)
endif()

target_include_directories(${_tgt_ty_interface}
  INTERFACE
    ${PROJECT_SOURCE_DIR}/include
    ${PROJECT_SOURCE_DIR}/libco
    ${PROJECT_SOURCE_DIR}/dtoa
    ${PROJECT_SOURCE_DIR}/src
)

if(TARGET GenerateLirHeader)
  add_dependencies(${_tgt_ty_interface} GenerateLirHeader)
endif()

target_compile_definitions(${_tgt_ty_interface}
  INTERFACE
    $<$<OR:$<C_COMPILER_ID:GNU>,$<PLATFORM_ID:Linux>>:_GNU_SOURCE>
    $<$<NOT:$<CONFIG:Debug>>:TY_RELEASE>
    $<$<BOOL:${TY_SYSMALLOC}>:TY_SYSMALLOC>
    $<$<NOT:$<BOOL:${TY_LOG}>>:TY_NO_LOG>
    TY_HAVE_VERSION_INFO
    PCRE2_CODE_UNIT_WIDTH=8
    XXH_INLINE_ALL
    XXH_STATIC_LINKING_ONLY
    $<$<CONFIG:Debug>:XXH_NO_INLINE_HINTS=1>
)

# ---
#  define ty targets
# ---

set(_tgt_ty ${PROJECT_NAME})
add_executable(${_tgt_ty})
target_sources(${_tgt_ty} PRIVATE ty.c)
target_link_libraries(${_tgt_ty} PRIVATE ${_tgt_ty_interface})

string(TOUPPER "${CMAKE_BUILD_TYPE}" _ty_cfg)
set(_ty_tp "$<TARGET_PROPERTY:${_tgt_ty},")
file(GENERATE OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/BuildFlags.txt CONTENT
"${CMAKE_C_COMPILER} ${CMAKE_C_FLAGS} ${CMAKE_C_FLAGS_${_ty_cfg}} ${CMAKE_C${CMAKE_C_STANDARD}_STANDARD_COMPILE_OPTION} $<JOIN:$<LIST:TRANSFORM,$<LIST:FILTER,${_ty_tp}COMPILE_DEFINITIONS>,EXCLUDE,^$>,PREPEND,-D>, > $<JOIN:${_ty_tp}COMPILE_OPTIONS>, >
${CMAKE_EXE_LINKER_FLAGS} ${CMAKE_EXE_LINKER_FLAGS_${_ty_cfg}} $<JOIN:${_ty_tp}LINK_OPTIONS>, >
")
add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/BuildFlags.h
  COMMAND ${CMAKE_COMMAND} -DIN=${CMAKE_CURRENT_BINARY_DIR}/BuildFlags.txt -DOUT=${CMAKE_CURRENT_BINARY_DIR}/BuildFlags.h -P ${PROJECT_SOURCE_DIR}/cmake/BuildFlags.cmake
  DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/BuildFlags.txt ${PROJECT_SOURCE_DIR}/cmake/BuildFlags.cmake
)
target_sources(${_tgt_ty} PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/BuildFlags.h)
target_include_directories(${_tgt_ty} PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
target_compile_definitions(${_tgt_ty} PRIVATE
  $<$<BOOL:${TY_PGO_GENERATE}>:TY_BUILD_PGO="generate">
  $<$<BOOL:${TY_PGO_USE}>:TY_BUILD_PGO="use">
  $<$<BOOL:${TY_BOLT}>:TY_BUILD_BOLT>
)

# ---
#  install rules
# ---

include(GNUInstallDirs)
install(TARGETS ${_tgt_ty}
  COMPONENT InstallComponentTy
  DESTINATION ${CMAKE_INSTALL_BINDIR}
)

install(CODE
  "execute_process(COMMAND \"${CMAKE_COMMAND}\" -E create_symlink ty \"\$ENV{DESTDIR}\${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_BINDIR}/tpm\")"
  COMPONENT InstallComponentTy
)

if(NOT TY_EMBED_LIB)
  install(DIRECTORY ${PROJECT_SOURCE_DIR}/lib/
    COMPONENT InstallComponentTy
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/ty
    FILES_MATCHING PATTERN "*.ty"
    PATTERN ".history" EXCLUDE
    PERMISSIONS
      OWNER_READ OWNER_WRITE   # 6
      GROUP_READ               # 4
      WORLD_READ               # 4
  )
endif()

if(TY_PGO_GENERATE OR TY_PGO_USE)
  foreach(_tool IN ITEMS tybi minilua tyembed)
    if(TARGET ${_tool})
      target_compile_options(${_tool} PRIVATE -fno-profile-generate -fno-profile-use)
      target_link_options(${_tool} PRIVATE -fno-profile-generate -fno-profile-use)
    endif()
  endforeach()
endif()

# ---
#  include cpack (must be very last thing in cmakelists.txt)
# ---

include(${PROJECT_SOURCE_DIR}/cmake/CPackSetup.cmake)
