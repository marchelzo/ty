# FindSystemDeps.cmake
#
# When USE_SYSTEM_DEPS is ON (e.g. FreeBSD ports builds), find libraries
# and create IMPORTED targets that match the names expected by the rest of
# CMakeLists.txt (i.e. the vcpkg target names).
#
# Prefers static libraries (.a) to produce a self-contained binary.
#

include(FindPkgConfig)

# Helper: find a static library and its headers, create an IMPORTED STATIC target.
# Uses pkg-config for include dirs but links the .a directly.
function(_find_static_dep TARGET_NAME PC_NAME LIB_NAMES HEADER)
  pkg_check_modules(_pc_${PC_NAME} QUIET ${PC_NAME})

  # Find the static library
  find_library(_lib_${PC_NAME}
    NAMES ${LIB_NAMES}
    HINTS ${_pc_${PC_NAME}_LIBRARY_DIRS}
  )

  # Find the header
  find_path(_inc_${PC_NAME}
    NAMES ${HEADER}
    HINTS ${_pc_${PC_NAME}_INCLUDE_DIRS}
  )

  if(NOT _lib_${PC_NAME})
    message(FATAL_ERROR "${PC_NAME}: static library not found (searched: ${LIB_NAMES})")
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

# --- libffi ---
_find_static_dep(unofficial::libffi::libffi libffi "libffi.a;ffi" ffi.h)

# --- sqlite3 ---
_find_static_dep(unofficial::sqlite3::sqlite3 sqlite3 "libsqlite3.a;sqlite3" sqlite3.h)

# --- utf8proc ---
_find_static_dep(utf8proc::utf8proc libutf8proc "libutf8proc.a;utf8proc" utf8proc.h)

# --- pcre2 ---
_find_static_dep(PCRE2::8BIT libpcre2-8 "libpcre2-8.a;pcre2-8" pcre2.h)

# --- xxHash ---
_find_static_dep(xxHash::xxhash libxxhash "libxxhash.a;xxhash" xxhash.h)

# --- mimalloc ---
find_library(_mi_lib NAMES libmimalloc-static.a mimalloc-static libmimalloc.a mimalloc)
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
  message(FATAL_ERROR "mimalloc: static library not found. Install devel/mimalloc.")
endif()
