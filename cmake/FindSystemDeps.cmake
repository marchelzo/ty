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

# Helper: find a .a file by exact filename using pkg-config hints.
function(_find_static_dep TARGET_NAME PC_NAME STATIC_FILENAME HEADER)
  pkg_check_modules(_pc_${PC_NAME} QUIET ${PC_NAME})

  find_file(_lib_${PC_NAME} "${STATIC_FILENAME}"
    PATHS ${_pc_${PC_NAME}_LIBRARY_DIRS} /usr/local/lib /usr/lib
    NO_DEFAULT_PATH
  )

  find_path(_inc_${PC_NAME}
    NAMES ${HEADER}
    HINTS ${_pc_${PC_NAME}_INCLUDE_DIRS}
  )

  if(NOT _lib_${PC_NAME})
    message(FATAL_ERROR "${PC_NAME}: ${STATIC_FILENAME} not found")
  endif()
  if(NOT _inc_${PC_NAME})
    message(FATAL_ERROR "${PC_NAME}: header '${HEADER}' not found")
  endif()

  if(NOT TARGET ${TARGET_NAME})
    add_library(${TARGET_NAME} IMPORTED STATIC)
    set_target_properties(${TARGET_NAME} PROPERTIES
      IMPORTED_LOCATION "${_lib_${PC_NAME}}"
      INTERFACE_INCLUDE_DIRECTORIES "${_inc_${PC_NAME}}"
    )
  endif()
endfunction()

# --- static deps ---
_find_static_dep(unofficial::libffi::libffi libffi libffi.a ffi.h)
_find_static_dep(PCRE2::8BIT libpcre2-8 libpcre2-8.a pcre2.h)
_find_static_dep(xxHash::xxhash libxxhash libxxhash.a xxhash.h)

# --- mimalloc (static) ---
find_file(_mi_lib "libmimalloc.a"
  PATHS /usr/local/lib /usr/lib
  NO_DEFAULT_PATH
)
find_path(_mi_inc NAMES mimalloc.h PATH_SUFFIXES mimalloc)
if(_mi_lib AND _mi_inc)
  if(NOT TARGET mimalloc-static)
    add_library(mimalloc-static IMPORTED STATIC)
    set_target_properties(mimalloc-static PROPERTIES
      IMPORTED_LOCATION "${_mi_lib}"
      INTERFACE_INCLUDE_DIRECTORIES "${_mi_inc}"
      IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
    )
  endif()
else()
  message(FATAL_ERROR "mimalloc: libmimalloc.a not found. Install devel/mimalloc.")
endif()

# --- shared deps (no .a available on FreeBSD) ---
pkg_check_modules(_utf8proc REQUIRED IMPORTED_TARGET libutf8proc)
if(NOT TARGET utf8proc::utf8proc)
  add_library(utf8proc::utf8proc ALIAS PkgConfig::_utf8proc)
endif()

pkg_check_modules(_sqlite3 REQUIRED IMPORTED_TARGET sqlite3)
if(NOT TARGET unofficial::sqlite3::sqlite3)
  add_library(unofficial::sqlite3::sqlite3 ALIAS PkgConfig::_sqlite3)
endif()
