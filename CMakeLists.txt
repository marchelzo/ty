cmake_minimum_required(VERSION 3.21)

project(ty VERSION 0.1 LANGUAGES C)

include(cmake/VersionInfoTarget.cmake)

# ---
#   user-defined options
# ---
option(BUILD_PROFILER "Build the typrof executable" OFF)

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
  find_package(PkgConfig)
  pkg_check_modules(READLINE REQUIRED readline)
  add_library(unofficial-readline STATIC IMPORTED)
  target_link_libraries(unofficial-readline INTERFACE "${READLINE_STATIC_LIBRARIES}")
  target_include_directories(unofficial-readline INTERFACE "${READLINE_INCLUDE_DIRS}")
  target_link_directories(unofficial-readline INTERFACE "${READLINE_LIBRARY_DIRS}")
  list(GET READLINE_LINK_LIBRARIES 0 _readline_imported_location)
  set_target_properties(unofficial-readline PROPERTIES IMPORTED_LOCATION ${_readline_imported_location})
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

set(_tgt_ty_interface "${PROJECT_NAME}_Objects")
add_library(${_tgt_ty_interface} INTERFACE)

set(_tgt_ty_interface_version_info "${_tgt_ty_interface}_VersionInfo")
add_version_info_target(NAME ${_tgt_ty_interface_version_info} LANGUAGE C)

target_compile_options(${_tgt_ty_interface}
  INTERFACE
    $<$<CXX_COMPILER_ID:GNU>:-Wall -Wno-switch -Wno-unused-value -Wno-unused-function>
    $<$<CXX_COMPILER_ID:Clang>:-Weverything>
    $<$<CXX_COMPILER_ID:MSVC>:/W4>
)

target_sources(${_tgt_ty_interface}
  INTERFACE
    ${_src_files}
)

target_link_libraries(${_tgt_ty_interface}
  INTERFACE
    ${_tgt_ty_interface_version_info}
    Threads::Threads # pthreads (or equivalent)
    $<$<NOT:$<BOOL:${WIN32}>>:${CMAKE_DL_LIBS}>
    CURL::libcurl
    OpenSSL::SSL
    OpenSSL::Crypto
    unofficial::libffi::libffi
    unofficial::sqlite3::sqlite3
    unofficial::gumbo::gumbo
    unofficial::pcre::pcre
    utf8proc
    $<$<NOT:$<BOOL:${WIN32}>>:unofficial-readline>
    $<$<NOT:$<BOOL:${WIN32}>>:m>
    $<$<BOOL:${WIN32}>:unofficial::readline-win32::readline>
    $<$<BOOL:${WIN32}>:unofficial::getopt-win32::getopt>
    $<$<BOOL:${WIN32}>:ws2_32> # winsock2
)

target_include_directories(${_tgt_ty_interface}
  INTERFACE
    ${PROJECT_SOURCE_DIR}/include
)

target_compile_definitions(${_tgt_ty_interface}
  INTERFACE
    $<$<C_COMPILER_ID:GNU>:_GNU_SOURCE>
    $<$<NOT:$<CONFIG:Debug>>:TY_RELEASE>
    $<$<NOT:$<CONFIG:Debug>>:TY_NO_LOG>
    TY_RELEASE
    TY_NO_LOG
    TY_HAVE_VERSION_INFO
)

# ---
#  define ty targets
# ---

set(_tgt_ty ${PROJECT_NAME})
add_executable(${_tgt_ty})
target_link_libraries(${_tgt_ty} PRIVATE ${_tgt_ty_interface})

if(BUILD_PROFILER)
  set(_tgt_ty_profiler "${PROJECT_NAME}prof")
  add_executable(${_tgt_ty_profiler})
  target_compile_definitions(${_tgt_ty_profiler} PRIVATE TY_ENABLE_PROFILING)
  target_link_libraries(${_tgt_ty_profiler} PRIVATE ${_tgt_ty_interface})
endif()

# ---
#  install rules
# ---

include(GNUInstallDirs)
install(TARGETS ${_tgt_ty} ${_tgt_ty_profiler}
  DESTINATION ${CMAKE_INSTALL_BINDIR}
)
