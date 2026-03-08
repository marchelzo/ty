cmake_minimum_required(VERSION 3.25)

project(ty VERSION 0.1 LANGUAGES C)

include(cmake/VersionInfoTarget.cmake)

# ---
#   user-defined options
# ---

option(BUILD_PROFILER "Build the typrof executable for profiling" OFF)
option(USE_NSYNC "Use nsync synchronization primitives on supported platforms" ON)
option(NO_JIT "Disable JIT code generation" OFF)

# ---
#   find 3rd-party dependencies
# ---

# defines target(s): Threads::Threads
find_package(Threads REQUIRED)
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
# defines target(s): nsync
find_package(nsync CONFIG REQUIRED)
add_library(nsync::nsync ALIAS nsync) #<-- sadly nsync doesnt do this for us
# defines target(s): mimalloc, mimalloc-static
find_package(mimalloc CONFIG REQUIRED)
set_target_properties(mimalloc-static PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
)

# ---
#   global compiler variables
# ---

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Enable LTO globally so vendored libs (libco, dtoa, etc.) also participate
include(CheckIPOSupported)
check_ipo_supported(RESULT _lto_supported OUTPUT _lto_error)
if(_lto_supported)
  set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()

# ---
#  vendored libraries
# ---

add_subdirectory(vendored)

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
else()
  set(_tgt_gen_errno_h GenerateErrnoConstantsH)
  add_custom_target(${_tgt_gen_errno_h}
    BYPRODUCTS
      ${_file_errno_constants_h}
    COMMAND # generate tmp file
      sh "${_gen_errno_script}" > "${_file_errno_constants_h}.tmp"
    COMMAND # replace existing (if different)
      ${CMAKE_COMMAND} -E copy_if_different
        "${_file_errno_constants_h}.tmp"
        "${_file_errno_constants_h}"
    COMMAND # remove tmp file
      ${CMAKE_COMMAND} -E rm "${_file_errno_constants_h}.tmp"
    WORKING_DIRECTORY
      "${PROJECT_SOURCE_DIR}"
    COMMENT
      "Generating errno_constants.h file using geterrnos.sh"
    DEPENDS
      ${_gen_errno_script}
    VERBATIM
  )
  add_dependencies(${_tgt_errnoconstants_h} ${_tgt_gen_errno_h})
endif()

# ---
#  generate keyword perfect hash
# ---

set(_file_keywords_h  ${_autogen_dir}/include/keywords.h)
set(_gperf_input      ${PROJECT_SOURCE_DIR}/src/keywords.gperf)

set(_tgt_keywords_h "KeywordsH")
add_library(${_tgt_keywords_h} INTERFACE)
target_include_directories(${_tgt_keywords_h}
  INTERFACE
    ${_autogen_dir}/include
)

find_program(GPERF_EXECUTABLE gperf)
if(GPERF_EXECUTABLE)
  add_custom_command(
    OUTPUT
      ${_file_keywords_h}
    COMMAND
      ${GPERF_EXECUTABLE} "${_gperf_input}" > "${_file_keywords_h}.tmp"
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

# ---
#  DynASM JIT code generation
# ---

find_program(LUAJIT_EXECUTABLE luajit REQUIRED
  HINTS "${VCPKG_INSTALLED_DIR}/${VCPKG_TARGET_TRIPLET}/tools/luajit"
)
if(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64|ARM64")
  set(_jit_dasc ${PROJECT_SOURCE_DIR}/src/jit_arm64.dasc)
  set(_jit_hdr  ${PROJECT_SOURCE_DIR}/src/jit_arm64.h)
else()
  set(_jit_dasc ${PROJECT_SOURCE_DIR}/src/jit_x64.dasc)
  set(_jit_hdr  ${PROJECT_SOURCE_DIR}/src/jit_x64.h)
endif()

add_custom_command(
  OUTPUT ${_jit_hdr}
  COMMAND ${LUAJIT_EXECUTABLE} ${PROJECT_SOURCE_DIR}/LuaJIT/dynasm/dynasm.lua
    -o ${_jit_hdr} ${_jit_dasc}
  DEPENDS ${_jit_dasc}
  COMMENT "Generating JIT emission header from ${_jit_dasc}"
  VERBATIM
)
add_custom_target(GenerateJitHeader DEPENDS ${_jit_hdr})

# ---
#  target: ty
# ---

set(_src_files
  src/alloc.c
  src/array.c
  src/ast.c
  src/blob.c
  src/class.c
  src/compiler.c
  src/queue.c
  src/dict.c
  src/ffi.c
  src/functions.c
  src/gc.c
  src/highlight.c
  src/jit.c
  src/intern.c
  src/itable.c
  src/json.c
  src/lex.c
  src/object.c
  src/operators.c
  src/panic.c
  src/parse.c
  src/scope.c
  src/sqlite.c
  src/str.c
  src/table.c
  src/tags.c
  src/token.c
  src/types.c
  src/util.c
  src/value.c
  src/vm.c
)

set(_tgt_ty_interface "${PROJECT_NAME}_Objects")
add_library(${_tgt_ty_interface} INTERFACE)

set(_tgt_ty_interface_version_info "${_tgt_ty_interface}_VersionInfo")
add_version_info_target(NAME ${_tgt_ty_interface_version_info}
  GIT_WORK_TREE ${PROJECT_SOURCE_DIR}
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
      -flto
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
      -mcpu=native
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
      -mcpu=native
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

target_link_libraries(${_tgt_ty_interface}
  INTERFACE
    ${_tgt_ty_interface_version_info}
    ${_tgt_ioctlconstants_h}
    ${_tgt_errnoconstants_h}
    ${_tgt_keywords_h}
    vendored::libco
    vendored::libmd
    vendored::dtoa
    $<LINK_LIBRARY:WHOLE_ARCHIVE,vendored::unibilium>
    $<$<BOOL:${USE_NSYNC}>:nsync::nsync>
    Threads::Threads # pthreads (or equivalent)
    mimalloc-static
    xxHash::xxhash
    utf8proc::utf8proc
    PCRE2::8BIT
    unofficial::libffi::libffi
    unofficial::sqlite3::sqlite3
    $<$<NOT:$<BOOL:${WIN32}>>:${CMAKE_DL_LIBS}>
    $<$<NOT:$<BOOL:${WIN32}>>:m>
    $<$<BOOL:${WIN32}>:ws2_32> # winsock2
    $<$<BOOL:${WIN32}>:Shlwapi.lib>
)

if(USE_NSYNC)
  target_link_libraries(${_tgt_ty_interface} INTERFACE nsync)
endif()

target_include_directories(${_tgt_ty_interface}
  INTERFACE
    ${PROJECT_SOURCE_DIR}/include
    ${PROJECT_SOURCE_DIR}/src
)

if(TARGET GenerateJitHeader)
  add_dependencies(${_tgt_ty_interface} GenerateJitHeader)
endif()

target_compile_definitions(${_tgt_ty_interface}
  INTERFACE
    $<$<C_COMPILER_ID:GNU>:_GNU_SOURCE>
    $<$<NOT:$<CONFIG:Debug>>:TY_RELEASE>
    $<$<BOOL:${NO_JIT}>:TY_NO_JIT>
    $<$<BOOL:${USE_NSYNC}>:TY_USE_NSYNC>
    $<$<NOT:$<CONFIG:Debug>>:TY_NO_LOG>
    TY_HAVE_VERSION_INFO
    PCRE2_CODE_UNIT_WIDTH=8
    XXH_INLINE_ALL
    XXH_STATIC_LINKING_ONLY
)

# ---
#  define ty targets
# ---

set(_tgt_ty ${PROJECT_NAME})
add_executable(${_tgt_ty})
target_sources(${_tgt_ty} PRIVATE ty.c)
target_link_libraries(${_tgt_ty} PRIVATE ${_tgt_ty_interface})

set(_tgt_ty_ls "${PROJECT_NAME}ls")
add_executable(${_tgt_ty_ls})
target_sources(${_tgt_ty_ls} PRIVATE tyls.c)
target_compile_definitions(${_tgt_ty_ls} PRIVATE TY_LS)
target_link_libraries(${_tgt_ty_ls} PRIVATE ${_tgt_ty_interface})

if(BUILD_PROFILER)
  set(_tgt_ty_profiler "${PROJECT_NAME}prof")
  add_executable(${_tgt_ty_profiler})
  target_sources(${_tgt_ty_profiler} PRIVATE ty.c)
  target_compile_definitions(${_tgt_ty_profiler} PRIVATE TY_PROFILER)
  target_link_libraries(${_tgt_ty_profiler} PRIVATE ${_tgt_ty_interface})
endif()

# export symbols (essentially adds the equivalent of: -rdynamic during link)
foreach(_tgt IN ITEMS ${_tgt_ty} ${_tgt_tyls} ${_tgt_typrof})
  set_target_properties(${_tgt} PROPERTIES ENABLE_EXPORTS ON)
endforeach()

# ---
#  install rules
# ---

include(GNUInstallDirs)
install(TARGETS ${_tgt_ty} ${_tgt_ty_profiler} ${_tgt_ty_ls}
  COMPONENT InstallComponentTy
  DESTINATION ${CMAKE_INSTALL_BINDIR}
)

install(DIRECTORY ${PROJECT_SOURCE_DIR}/lib/
  COMPONENT InstallComponentTy
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/ty
  FILES_MATCHING PATTERN "*.ty"
  PERMISSIONS
    OWNER_READ OWNER_WRITE   # 6
    GROUP_READ               # 4
    WORLD_READ               # 4
)

# ---
#  include cpack (must be very last thing in cmakelists.txt)
# ---

include(${PROJECT_SOURCE_DIR}/cmake/CPackSetup.cmake)
