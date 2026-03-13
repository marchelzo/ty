cmake_minimum_required(VERSION 3.10)
project(unibilium VERSION 2.0.0 LANGUAGES C)

if(NOT WIN32)
  set(_terminfo_candidates
    /etc/terminfo
    /lib/terminfo
    /usr/share/terminfo
    /usr/share/misc/terminfo
    /usr/lib/terminfo
    /usr/local/share/terminfo
    /usr/local/lib/terminfo
    /usr/share/lib/terminfo
  )
  set(_terminfo_found "")
  foreach(_d IN LISTS _terminfo_candidates)
    if(IS_DIRECTORY "${_d}")
      if(_terminfo_found)
        string(APPEND _terminfo_found ":${_d}")
      else()
        set(_terminfo_found "${_d}")
      endif()
    endif()
  endforeach()
  if(NOT _terminfo_found)
    string(JOIN ":" _terminfo_found ${_terminfo_candidates})
  endif()
  set(TERMINFO_DIRS "${_terminfo_found}")
else()
  set(TERMINFO_DIRS "")
endif()

add_library(unibilium STATIC
  unibilium.c
  uninames.c
  uniutil.c
)

target_compile_definitions(unibilium PRIVATE
  TERMINFO_DIRS="${TERMINFO_DIRS}"
)

target_compile_options(unibilium PRIVATE
  -Wall
  -O2
  -std=c99
)

set_target_properties(unibilium PROPERTIES
  POSITION_INDEPENDENT_CODE ON
)

target_include_directories(unibilium PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
  $<INSTALL_INTERFACE:include>
)
