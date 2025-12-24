cmake_minimum_required(VERSION 3.10)
project(unibilium VERSION 2.0.0 LANGUAGES C)

if(NOT WIN32)
  execute_process(
    COMMAND sh -c "ncursesw6-config --terminfo-dirs 2>/dev/null || \
                   ncurses6-config  --terminfo-dirs 2>/dev/null || \
                   ncursesw5-config --terminfo-dirs 2>/dev/null || \
                   ncurses5-config  --terminfo-dirs 2>/dev/null || \
                   echo '/etc/terminfo:/lib/terminfo:/usr/share/terminfo:/usr/lib/terminfo:/usr/local/share/terminfo:/usr/local/lib/terminfo'"
    OUTPUT_VARIABLE TERMINFO_DIRS
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
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
