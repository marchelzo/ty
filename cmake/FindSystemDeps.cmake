# FindSystemDeps.cmake
#
# When USE_SYSTEM_DEPS is ON (e.g. FreeBSD ports builds), find libraries
# and create IMPORTED targets that match the names expected by the rest of
# CMakeLists.txt (i.e. the vcpkg target names).
#
# Statically links: libffi, mimalloc, pcre2, xxhash
# Dynamically links: utf8proc, sqlite3 (no .a available on FreeBSD)
#

include(FindPkgConfig)

# --- libffi (static) ---
pkg_check_modules(_pc_ffi QUIET libffi)
find_path(_ffi_inc NAMES ffi.h HINTS ${_pc_ffi_INCLUDE_DIRS})
if(NOT _ffi_inc)
  message(FATAL_ERROR "libffi: ffi.h not found")
endif()
add_library(unofficial::libffi::libffi IMPORTED STATIC)
set_target_properties(unofficial::libffi::libffi PROPERTIES
  IMPORTED_LOCATION "/usr/local/lib/libffi.a"
  INTERFACE_INCLUDE_DIRECTORIES "${_ffi_inc}"
)

# --- pcre2 (static) ---
pkg_check_modules(_pc_pcre2 QUIET libpcre2-8)
find_path(_pcre2_inc NAMES pcre2.h HINTS ${_pc_pcre2_INCLUDE_DIRS})
if(NOT _pcre2_inc)
  message(FATAL_ERROR "pcre2: pcre2.h not found")
endif()
add_library(PCRE2::8BIT IMPORTED STATIC)
set_target_properties(PCRE2::8BIT PROPERTIES
  IMPORTED_LOCATION "/usr/local/lib/libpcre2-8.a"
  INTERFACE_INCLUDE_DIRECTORIES "${_pcre2_inc}"
)

# --- xxhash (static) ---
pkg_check_modules(_pc_xxhash QUIET libxxhash)
find_path(_xxhash_inc NAMES xxhash.h HINTS ${_pc_xxhash_INCLUDE_DIRS})
if(NOT _xxhash_inc)
  message(FATAL_ERROR "xxhash: xxhash.h not found")
endif()
add_library(xxHash::xxhash IMPORTED STATIC)
set_target_properties(xxHash::xxhash PROPERTIES
  IMPORTED_LOCATION "/usr/local/lib/libxxhash.a"
  INTERFACE_INCLUDE_DIRECTORIES "${_xxhash_inc}"
)

# --- mimalloc (static) ---
find_path(_mi_inc NAMES mimalloc.h PATH_SUFFIXES mimalloc)
if(NOT _mi_inc)
  message(FATAL_ERROR "mimalloc: mimalloc.h not found")
endif()
add_library(mimalloc-static IMPORTED STATIC)
set_target_properties(mimalloc-static PROPERTIES
  IMPORTED_LOCATION "/usr/local/lib/libmimalloc.a"
  INTERFACE_INCLUDE_DIRECTORIES "${_mi_inc}"
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
)

# --- utf8proc (shared) ---
pkg_check_modules(_utf8proc REQUIRED IMPORTED_TARGET libutf8proc)
add_library(utf8proc::utf8proc ALIAS PkgConfig::_utf8proc)

# --- sqlite3 (shared) ---
pkg_check_modules(_sqlite3 REQUIRED IMPORTED_TARGET sqlite3)
add_library(unofficial::sqlite3::sqlite3 ALIAS PkgConfig::_sqlite3)
