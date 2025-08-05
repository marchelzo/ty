cmake_minimum_required(VERSION 3.21)

project(ty VERSION 0.1 LANGUAGES C)

include(cmake/VersionInfoTarget.cmake)

# ---
#   user-defined options
# ---

option(BUILD_PROFILER "Build the typrof executable for profiling" OFF)

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
# defines target(s): PCRE2::8BIT, PCRE2::16BIT, PCRE2::32BIT, PCRE2::POSIX
find_package(pcre2 CONFIG REQUIRED)
# defines target(s): CURL::libcurl
find_package(CURL CONFIG REQUIRED)
# defines target(s): OpenSSL::SSL, OpenSSL::Crypto, OpenSSL::applink
find_package(OpenSSL REQUIRED)

# ---
#   global compiler variables
# ---

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# ---
#  generate ioctl_constants
# ---

set(_autogen_dir ${PROJECT_BINARY_DIR}/GeneratedFiles)
file(MAKE_DIRECTORY ${_autogen_dir})
file(MAKE_DIRECTORY ${_autogen_dir}/include)

set(_file_ioctl_constants_h ${_autogen_dir}/include/ioctl_constants.h)
set(_gen_ioctl_script       ${PROJECT_SOURCE_DIR}/scripts/getioctls.sh)

set(_tgt_ioctlconstants_h "IoctlConstantsH")
add_library(${_tgt_ioctlconstants_h} INTERFACE)
target_include_directories(${_tgt_ioctlconstants_h}
  INTERFACE
    ${_autogen_dir}/include
)

if (WIN32)
  if (NOT EXISTS ${_file_ioctl_constants_h})
    file(TOUCH ${_file_ioctl_constants_h})
  endif()
else()
  set(_tgt_gen_ioctl_h GenerateIoctlConstantsH)
  add_custom_target(${_tgt_gen_ioctl_h}
    BYPRODUCTS
      ${_file_ioctl_constants_h}
    COMMAND # generate tmp file
      sh "${_gen_ioctl_script}" > "${_file_ioctl_constants_h}.tmp"
    COMMAND # replace existing (if different)
      ${CMAKE_COMMAND} -E copy_if_different
        "${_file_ioctl_constants_h}.tmp"
        "${_file_ioctl_constants_h}"
    COMMAND # remove tmp file
      ${CMAKE_COMMAND} -E rm "${_file_ioctl_constants_h}.tmp"
    WORKING_DIRECTORY
      "${PROJECT_SOURCE_DIR}"
    COMMENT
      "Generating ioctl_constants.h file using getioctls.sh"
    DEPENDS
      ${_gen_ioctl_script}
    VERBATIM
  )
  add_dependencies(${_tgt_ioctlconstants_h} ${_tgt_gen_ioctl_h})
endif()

# ---
#  target: libco
# ---
add_library(libco)
target_sources(libco PRIVATE libco/libco.c)
target_compile_definitions(libco PRIVATE LIBCO_MP)

# ---
#  target: dtoa
# ---
add_library(dtoa)
target_sources(dtoa PRIVATE dtoa/SwiftDtoa.c)

# ---
#  target: ty
# ---

set(_src_files
  src/alloc.c
  src/array.c
  src/ast.c
  src/blob.c
  src/class.c
  src/compiler.c
  src/curl.c
  src/dict.c
  src/ffi.c
  src/functions.c
  src/gc.c
  src/html.c
  src/intern.c
  src/itable.c
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
  src/types.c
  src/util.c
  src/value.c
  src/vm.c
)

set(_tgt_ty_interface "${PROJECT_NAME}_Objects")
add_library(${_tgt_ty_interface} INTERFACE)

set(_tgt_ty_interface_version_info "${_tgt_ty_interface}_VersionInfo")
add_version_info_target(NAME ${_tgt_ty_interface_version_info}
  GIT_WORK_TREE ${PROJECT_SOURCE_DIR}
  LANGUAGE C
)

target_compile_options(${_tgt_ty_interface}
  INTERFACE
    $<$<C_COMPILER_ID:GNU>:
      -Wall
      -Wno-switch
      -Wno-unused-value
      -Wno-unused-function
      -Wno-multichar
      -Wno-trigraphs
      -flto
      -pipe
    >
    $<$<C_COMPILER_ID:AppleClang>:
      -Wall
      -Wno-class-varargs
      -Wno-switch
      -Wno-string-plus-int
      -Wno-multichar
      -Wno-trigraphs
      -Wno-sign-compare
      -Wno-sign-conversion
      -Wno-padded
      -Wno-shadow
      -Wno-shorten-64-to-32
      -Wno-cast-qual
      -Wno-declaration-after-statement
      -mcpu=native
      -flto
      -ferror-limit=3
    >
    $<$<C_COMPILER_ID:Clang>:
      -Wall
      -Wno-class-varargs
      -Wno-switch
      -Wno-string-plus-int
      -Wno-multichar
      -Wno-trigraphs
      -Wno-sign-compare
      -Wno-sign-conversion
      -Wno-padded
      -Wno-shadow
      -Wno-shorten-64-to-32
      -Wno-cast-qual
      -Wno-declaration-after-statement
      -mcpu=native
      -flto
    >
    $<$<C_COMPILER_ID:MSVC>:
      /W4
      /we4013 # undefined function, assuming extern returning int
    >
)

target_sources(${_tgt_ty_interface}
  INTERFACE
    ${_src_files}
)

target_link_libraries(${_tgt_ty_interface}
  INTERFACE
    ${_tgt_ty_interface_version_info}
    ${_tgt_ioctlconstants_h}
    Threads::Threads # pthreads (or equivalent)
    CURL::libcurl
    OpenSSL::SSL
    OpenSSL::Crypto
    unofficial::libffi::libffi
    unofficial::sqlite3::sqlite3
    unofficial::gumbo::gumbo
    PCRE2::8BIT
    utf8proc
    libco
    dtoa
    $<$<NOT:$<BOOL:${WIN33}>>:${CMAKE_DL_LIBS}>
    $<$<NOT:$<BOOL:${WIN32}>>:unofficial-readline>
    $<$<NOT:$<BOOL:${WIN32}>>:m>
    $<$<BOOL:${WIN32}>:unofficial::readline-win32::readline>
    $<$<BOOL:${WIN32}>:ws2_32> # winsock2
    $<$<BOOL:${WIN32}>:Shlwapi.lib>
)

target_include_directories(${_tgt_ty_interface}
  INTERFACE
    ${PROJECT_SOURCE_DIR}/include
    ${PROJECT_SOURCE_DIR}/libco
    ${PROJECT_SOURCE_DIR}/dtoa
)

target_compile_definitions(${_tgt_ty_interface}
  INTERFACE
    $<$<C_COMPILER_ID:GNU>:_GNU_SOURCE>
    $<$<NOT:$<CONFIG:Debug>>:TY_RELEASE>
    $<$<NOT:$<CONFIG:Debug>>:TY_NO_LOG>
    TY_RELEASE
    TY_NO_LOG
    TY_HAVE_VERSION_INFO
    PCRE2_CODE_UNIT_WIDTH=8
)

# ---
#  define ty targets
# ---

set(_tgt_ty ${PROJECT_NAME})
add_executable(${_tgt_ty})
target_sources(${_tgt_ty} PRIVATE ty.c)
target_link_libraries(${_tgt_ty} PRIVATE ${_tgt_ty_interface})

set(_tgt_ty_ls "${PROJECT_NAME}ls")
add_executable(${_tgt_ty_ls})
target_sources(${_tgt_ty_ls} PRIVATE tyls.c)
target_compile_definitions(${_tgt_ty_ls} PRIVATE TY_LS)
target_link_libraries(${_tgt_ty_ls} PRIVATE ${_tgt_ty_interface})

if(BUILD_PROFILER)
  set(_tgt_ty_profiler "${PROJECT_NAME}prof")
  add_executable(${_tgt_ty_profiler})
  target_sources(${_tgt_ty_profiler} PRIVATE ty.c)
  target_compile_definitions(${_tgt_ty_profiler} PRIVATE TY_PROFILER)
  target_link_libraries(${_tgt_ty_profiler} PRIVATE ${_tgt_ty_interface})
endif()

# ---
#  install rules
# ---

include(GNUInstallDirs)
install(TARGETS ${_tgt_ty} ${_tgt_ty_profiler} ${_tgt_ty_ls}
  COMPONENT InstallComponentTy
  DESTINATION ${CMAKE_INSTALL_BINDIR}
)

file(GLOB _ty_modules LIST_DIRECTORIES false ${PROJECT_SOURCE_DIR}/lib/*.ty)
install(FILES ${_ty_modules}
  COMPONENT InstallComponentTy
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/ty
  PERMISSIONS
    OWNER_READ OWNER_WRITE   # 6
    GROUP_READ               # 4
    WORLD_READ               # 4
)

# ---
#  include cpack (must be very last thing in cmakelists.txt)
# ---

include(${PROJECT_SOURCE_DIR}/cmake/CPackSetup.cmake)
