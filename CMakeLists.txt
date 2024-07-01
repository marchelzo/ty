cmake_minimum_required(VERSION 3.21)

project(ty VERSION 0.1 LANGUAGES C)

# ---
#   find 3rd-party dependencies
# ---

# defines target(s): Threads::Threads
find_package(Threads REQUIRED)
# defines target(s): unofficial::libffi::libffi
find_package(unofficial-libffi CONFIG REQUIRED)
# defines target(s): unofficial::sqlite3::sqlite3
find_package(unofficial-sqlite3 CONFIG REQUIRED)
# defines target(s): unofficial::gumbo::gumbo
find_package(unofficial-gumbo CONFIG REQUIRED)
# defines target(s): utf8proc
find_package(unofficial-utf8proc CONFIG REQUIRED)
if (WIN32)
  # defines target(s): unofficial::readline-win32::readline
  find_package(unofficial-readline-win32 CONFIG REQUIRED)
else()
  # defines target(s): unofficial::readline::readline
  find_package(unofficial-readline CONFIG REQUIRED)
endif()
# defines target(s): unofficial::pcre::pcre unofficial::pcre::pcre16 unofficial::pcre::pcre32 unofficial::pcre::pcrecpp
find_package(unofficial-pcre CONFIG REQUIRED)
# defines target(s): CURL::libcurl
find_package(CURL CONFIG REQUIRED)
# defines target(s): OpenSSL::SSL, OpenSSL::Crypto, OpenSSL::applink
find_package(OpenSSL REQUIRED)

if (WIN32)
  # defines target(s): unofficial::getopt-win32::getopt
  find_package(unofficial-getopt-win32 CONFIG REQUIRED)
endif()

if (WIN32)
  # the shitty cmake file for the PThreads4W pkg sets NO_DEFAULT_PATH so it
  # doesn't read the CMAKE_PREFIX_PATH value when trying to locate the libs
  # instead it searches using "VCPKG_INSTALLED_DIR" and "VCPKG_TARGET_TRIPLET"
  # defines target(s): PThreads4W::PThreads4W
  find_package(PThreads4W CONFIG REQUIRED)
endif()

# ---
#   global compiler variables
# ---

set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED TRUE)

# ---
#  target: ty
# ---

set(_src_files
  ty.c
  src/alloc.c
  src/array.c
  src/blob.c
  src/class.c
  src/compiler.c
  src/curl.c
  src/dict.c
  src/ffi.c
  src/functions.c
  src/gc.c
  src/html.c
  src/json.c
  src/lex.c
  src/object.c
  src/operators.c
  src/panic.c
  src/parse.c
  src/queue.c
  src/scope.c
  src/sqlite.c
  src/str.c
  src/table.c
  src/tags.c
  src/token.c
  src/util.c
  src/value.c
  src/vm.c
)

set(_tgt_ty "${PROJECT_NAME}")
add_executable(${_tgt_ty})

target_compile_options(${_tgt_ty}
  PRIVATE
    $<$<CXX_COMPILER_ID:GNU>:-Wall -Wno-switch -Wno-unused-value -Wno-unused-function>
    $<$<CXX_COMPILER_ID:Clang>:-Weverything>
    $<$<CXX_COMPILER_ID:MSVC>:/W4>
)

target_sources(${_tgt_ty}
  PRIVATE
    ${_src_files}
)

target_link_libraries(${_tgt_ty}
  PUBLIC
    Threads::Threads # pthreads (or equivalent)
    $<$<NOT:${WIN32}>:"${CMAKE_DL_LIBS}">
    CURL::libcurl
    OpenSSL::SSL
    OpenSSL::Crypto
    unofficial::libffi::libffi
    unofficial::sqlite3::sqlite3
    unofficial::gumbo::gumbo
    unofficial::pcre::pcre
    $<$<NOT:${WIN32}>:unofficial::readline::readline>
    $<${WIN32}:unofficial::readline-win32::readline>
    $<${WIN32}:PThreads4W::PThreads4W>
    $<${WIN32}:unofficial::getopt-win32::getopt>
    utf8proc
    $<${WIN32}:ws2_32> # winsock2
)

target_include_directories(${_tgt_ty}
  PUBLIC
    ${PROJECT_SOURCE_DIR}/include
)

target_compile_definitions(${_tgt_ty}
  PRIVATE
    $<$<C_COMPILER_ID:GNU>:_GNU_SOURCE>
)

# ---
#  install rules
# ---

include(GNUInstallDirs)
install(TARGETS ${_tgt_ty}
  DESTINATION ${CMAKE_INSTALL_BINDIR}
)
