# FindSystemDeps.cmake
#
# When USE_SYSTEM_DEPS is ON (e.g. FreeBSD ports builds), find libraries
# via pkg-config / find_library and create IMPORTED targets that match the
# names expected by the rest of CMakeLists.txt (i.e. the vcpkg target names).
#

include(FindPkgConfig)

# --- libffi ---
pkg_check_modules(_ffi REQUIRED IMPORTED_TARGET libffi)
if(NOT TARGET unofficial::libffi::libffi)
  add_library(unofficial::libffi::libffi ALIAS PkgConfig::_ffi)
endif()

# --- sqlite3 ---
pkg_check_modules(_sqlite3 REQUIRED IMPORTED_TARGET sqlite3)
if(NOT TARGET unofficial::sqlite3::sqlite3)
  add_library(unofficial::sqlite3::sqlite3 ALIAS PkgConfig::_sqlite3)
endif()

# --- utf8proc ---
pkg_check_modules(_utf8proc REQUIRED IMPORTED_TARGET libutf8proc)
if(NOT TARGET utf8proc::utf8proc)
  add_library(utf8proc::utf8proc ALIAS PkgConfig::_utf8proc)
endif()

# --- pcre2 ---
pkg_check_modules(_pcre2 REQUIRED IMPORTED_TARGET libpcre2-8)
if(NOT TARGET PCRE2::8BIT)
  add_library(PCRE2::8BIT ALIAS PkgConfig::_pcre2)
endif()

# --- xxHash ---
# xxHash may not ship a .pc file on all systems; try pkg-config first,
# fall back to find_library + find_path.
pkg_check_modules(_xxhash QUIET IMPORTED_TARGET libxxhash)
if(_xxhash_FOUND)
  if(NOT TARGET xxHash::xxhash)
    add_library(xxHash::xxhash ALIAS PkgConfig::_xxhash)
  endif()
else()
  find_library(_xxhash_lib NAMES xxhash)
  find_path(_xxhash_inc NAMES xxhash.h)
  if(_xxhash_lib AND _xxhash_inc)
    add_library(xxHash::xxhash IMPORTED INTERFACE)
    set_target_properties(xxHash::xxhash PROPERTIES
      INTERFACE_LINK_LIBRARIES "${_xxhash_lib}"
      INTERFACE_INCLUDE_DIRECTORIES "${_xxhash_inc}"
    )
  else()
    message(FATAL_ERROR "xxHash not found. Install devel/xxhash.")
  endif()
endif()

# --- mimalloc ---
# mimalloc installs a cmake config on some systems; try that first.
find_package(mimalloc CONFIG QUIET)
if(NOT mimalloc_FOUND)
  find_library(_mi_lib NAMES mimalloc-static mimalloc)
  find_path(_mi_inc NAMES mimalloc.h PATH_SUFFIXES mimalloc)
  if(_mi_lib AND _mi_inc)
    add_library(mimalloc-static IMPORTED STATIC)
    set_target_properties(mimalloc-static PROPERTIES
      IMPORTED_LOCATION "${_mi_lib}"
      INTERFACE_INCLUDE_DIRECTORIES "${_mi_inc}"
      IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
    )
  else()
    message(FATAL_ERROR "mimalloc not found. Install devel/mimalloc.")
  endif()
else()
  # mimalloc CONFIG found — make sure the static target exists
  if(NOT TARGET mimalloc-static)
    if(TARGET mimalloc)
      add_library(mimalloc-static ALIAS mimalloc)
    endif()
  endif()
  set_target_properties(mimalloc-static PROPERTIES
    IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
  )
endif()
