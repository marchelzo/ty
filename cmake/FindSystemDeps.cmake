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
add_library(unofficial::libffi::libffi INTERFACE IMPORTED)
set_target_properties(unofficial::libffi::libffi PROPERTIES
  INTERFACE_INCLUDE_DIRECTORIES "${_ffi_inc}"
  INTERFACE_LINK_LIBRARIES "-Wl,-Bstatic;-lffi;-Wl,-Bdynamic"
)

# --- pcre2 (static) ---
pkg_check_modules(_pc_pcre2 QUIET libpcre2-8)
find_path(_pcre2_inc NAMES pcre2.h HINTS ${_pc_pcre2_INCLUDE_DIRS})
if(NOT _pcre2_inc)
  message(FATAL_ERROR "pcre2: pcre2.h not found")
endif()
add_library(PCRE2::8BIT INTERFACE IMPORTED)
set_target_properties(PCRE2::8BIT PROPERTIES
  INTERFACE_INCLUDE_DIRECTORIES "${_pcre2_inc}"
  INTERFACE_LINK_LIBRARIES "-Wl,-Bstatic;-lpcre2-8;-Wl,-Bdynamic"
)

# --- xxhash (static) ---
pkg_check_modules(_pc_xxhash QUIET libxxhash)
find_path(_xxhash_inc NAMES xxhash.h HINTS ${_pc_xxhash_INCLUDE_DIRS})
if(NOT _xxhash_inc)
  message(FATAL_ERROR "xxhash: xxhash.h not found")
endif()
add_library(xxHash::xxhash INTERFACE IMPORTED)
set_target_properties(xxHash::xxhash PROPERTIES
  INTERFACE_INCLUDE_DIRECTORIES "${_xxhash_inc}"
  INTERFACE_LINK_LIBRARIES "-Wl,-Bstatic;-lxxhash;-Wl,-Bdynamic"
)

# --- mimalloc (static) ---
find_path(_mi_inc NAMES mimalloc.h PATH_SUFFIXES mimalloc)
if(NOT _mi_inc)
  message(FATAL_ERROR "mimalloc: mimalloc.h not found")
endif()
add_library(mimalloc-static INTERFACE IMPORTED)
set_target_properties(mimalloc-static PROPERTIES
  INTERFACE_INCLUDE_DIRECTORIES "${_mi_inc}"
  INTERFACE_LINK_LIBRARIES "-Wl,-Bstatic;-lmimalloc;-Wl,-Bdynamic"
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
)

# --- utf8proc (shared) ---
pkg_check_modules(_utf8proc REQUIRED IMPORTED_TARGET libutf8proc)
add_library(utf8proc::utf8proc ALIAS PkgConfig::_utf8proc)

# --- sqlite3 (shared) ---
pkg_check_modules(_sqlite3 REQUIRED IMPORTED_TARGET sqlite3)
add_library(unofficial::sqlite3::sqlite3 ALIAS PkgConfig::_sqlite3)
