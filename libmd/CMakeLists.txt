cmake_minimum_required(VERSION 3.15)

project(libmd VERSION 0.1.0 LANGUAGES C)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_EXTENSIONS ON)

include(GNUInstallDirs)
include(CheckIncludeFile)
include(CheckTypeSize)
include(CheckCCompilerFlag)
include(CheckLinkerFlag)
include(TestBigEndian)

set(LIBMD_ABI_MAJOR 0)
set(LIBMD_ABI_MINOR 1)
set(LIBMD_ABI_PATCH 0)
set(LIBMD_ABI "${LIBMD_ABI_MAJOR}.${LIBMD_ABI_MINOR}.${LIBMD_ABI_PATCH}")

test_big_endian(WORDS_BIGENDIAN)
check_include_file(unistd.h HAVE_UNISTD_H)
check_include_file(sys/types.h HAVE_SYS_TYPES_H)
check_include_file(sys/stat.h HAVE_SYS_STAT_H)
check_include_file(stdint.h HAVE_STDINT_H)
check_include_file(inttypes.h HAVE_INTTYPES_H)
check_type_size(off_t OFF_T)
check_type_size(size_t SIZE_T)
check_type_size(ssize_t SSIZE_T)

add_library(md
  src/md2.c
  src/md4.c
  src/md5.c
  src/rmd160.c
  src/sha1.c
  src/sha2.c
  src/md2hl.c
  src/md4hl.c
  src/md5hl.c
  src/rmd160hl.c
  src/sha1hl.c
  src/sha224hl.c
  src/sha256hl.c
  src/sha384hl.c
  src/sha512hl.c
  src/sha512_256hl.c
)

add_library(libmd::md ALIAS md)

set_target_properties(md PROPERTIES
  VERSION ${LIBMD_ABI}
  SOVERSION ${LIBMD_ABI_MAJOR}
  C_VISIBILITY_PRESET hidden
  OUTPUT_NAME md
)

target_include_directories(md
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
  PRIVATE
    ${CMAKE_CURRENT_BINARY_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/src
)

target_compile_definitions(md PRIVATE
  _GNU_SOURCE
  $<$<PLATFORM_ID:Darwin>:_DARWIN_C_SOURCE>
  $<$<PLATFORM_ID:SunOS>:__EXTENSIONS__>
  $<$<BOOL:${HAVE_UNISTD_H}>:HAVE_UNISTD_H>
  $<$<BOOL:${HAVE_SYS_TYPES_H}>:HAVE_SYS_TYPES_H>
  $<$<BOOL:${HAVE_SYS_STAT_H}>:HAVE_SYS_STAT_H>
  $<$<BOOL:${HAVE_STDINT_H}>:HAVE_STDINT_H>
  $<$<BOOL:${HAVE_INTTYPES_H}>:HAVE_INTTYPES_H>
  $<$<BOOL:${WORDS_BIGENDIAN}>:WORDS_BIGENDIAN>
)

if(NOT CMAKE_C_FLAGS)
  set(warning_flags
    -Wall -Wextra
    -Wbad-function-cast
    -Wcast-align
    -Wdeclaration-after-statement
    -Wformat=2
    -Winit-self
    -Wmissing-declarations
    -Wmissing-prototypes
    -Wnested-externs
    -Wno-unused-parameter
    -Wold-style-definition
    -Wpointer-arith
    -Wredundant-decls
    -Wshadow
    -Wstrict-prototypes
    -Wwrite-strings
  )
  
  foreach(flag ${warning_flags})
    string(REGEX REPLACE "[-=]" "_" flag_var ${flag})
    check_c_compiler_flag(${flag} HAVE${flag_var})
    if(HAVE${flag_var})
      target_compile_options(md PRIVATE ${flag})
    endif()
  endforeach()
endif()

option(ENABLE_SANITIZE "Enable compiler sanitizer support" OFF)
if(ENABLE_SANITIZE)
  target_compile_options(md PRIVATE -fsanitize=address -fsanitize=leak -fsanitize=undefined)
  target_link_options(md PRIVATE -fsanitize=address -fsanitize=leak -fsanitize=undefined)
endif()

target_compile_definitions(md PRIVATE
  _GNU_SOURCE
  $<$<PLATFORM_ID:Darwin>:_DARWIN_C_SOURCE>
  $<$<PLATFORM_ID:SunOS>:__EXTENSIONS__>
)

if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  check_linker_flag(C "-Wl,--version-script=${CMAKE_CURRENT_SOURCE_DIR}/src/libmd.map" HAVE_LINKER_VERSION_SCRIPT)
  if(HAVE_LINKER_VERSION_SCRIPT)
    target_link_options(md PRIVATE "-Wl,--version-script=${CMAKE_CURRENT_SOURCE_DIR}/src/libmd.map")
  endif()
endif()

install(TARGETS md
  EXPORT libmdTargets
  LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
)

install(DIRECTORY include/
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
  FILES_MATCHING PATTERN "*.h"
)

install(EXPORT libmdTargets
  FILE libmdTargets.cmake
  NAMESPACE libmd::
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/libmd
)
