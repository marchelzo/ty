# ---
#  target: nsync
# ---

if (USE_NSYNC)
  add_subdirectory(nsync)
  add_library(vendored::nsync ALIAS nsync)
endif()

# ---
#  target: unibilium
# ---

add_subdirectory(unibilium)
add_library(vendored::unibilium ALIAS unibilium)

# ---
#  target: md
# ---

add_subdirectory(libmd)
add_library(vendored::libmd ALIAS md)

# ---
#  target: libco
# ---

add_library(libco)
add_library(vendored::libco ALIAS libco)
target_sources(libco PRIVATE libco/libco.c)
target_include_directories(libco PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/libco)
target_compile_definitions(libco PRIVATE LIBCO_MP)

# ---
#  target: dtoa
# ---

add_library(dtoa)
add_library(vendored::dtoa ALIAS dtoa)
target_include_directories(dtoa PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/dtoa)
target_sources(dtoa PRIVATE dtoa/SwiftDtoa.c)
