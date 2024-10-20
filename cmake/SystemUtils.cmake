#
# determines host system information (normalized)
#
#  sets variables:
#    host_system_os, host_system_ver, host_distro_id, host_distro_version,
#    host_system_id, host_system_arch
#
# ex.
#                       | Windows 10 21H2 | Ubuntu 22.04        | CentOS 7.5
#   host_system_os      |  'windows'      | 'linux'             | 'linux'
#   host_system_ver     |  '10.0.19044'   | '5.15.0-83-generic' | '5.15.0-83-generic'
#   host_distro_id      |  ''             | 'ubuntu'            | 'centos'
#   host_distro_version |  ''             | '22.04'             | '7'
#   host_system_id      |  'windows'      | 'ubuntu-22.04'      | 'centos-7'
#   host_system_arch    |  'x64"          | 'x64'               | 'x86'
#
function(ty_query_host_system_info)

  # normalize the architecture type
  if (CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "i386|x86|x86_32|AMD64|x86_64|x64")
    if(CMAKE_SIZEOF_VOID_P EQUAL 8)
      set(_system_arch "x64")
    else()
      set(_system_arch "x86")
    endif()
  elseif (_system_arch MATCHES "ARM")
    if(CMAKE_SIZEOF_VOID_P EQUAL 8)
      set(_system_arch "ARM64")
    else()
      set(_system_arch "ARM32")
    endif()
  endif()

  # set system os and distro info
  if(CMAKE_HOST_SYSTEM_NAME MATCHES "[wW]indows")
    set(_system_os "windows")
    # -- method 1: use cmake_host_system_information()
    if ("${CMAKE_VERSION}" VERSION_GREATER_EQUAL 3.22.0)
      cmake_host_system_information(RESULT _distro_id      QUERY DISTRIB_ID)
      cmake_host_system_information(RESULT _distro_version QUERY DISTRIB_VERSION_ID)
    endif()

  elseif(CMAKE_HOST_SYSTEM_NAME MATCHES "[lL]inux")
    set(_system_os "linux")
    # -- method 1: use cmake_host_system_information()
    if ("${CMAKE_VERSION}" VERSION_GREATER_EQUAL 3.22.0)
      cmake_host_system_information(RESULT _distro_id      QUERY DISTRIB_ID)
      cmake_host_system_information(RESULT _distro_version QUERY DISTRIB_VERSION_ID)

    # -- method 2: use /etc/os-release ... manually
    elseif(EXISTS "/etc/os-release")
      file(STRINGS "/etc/os-release" _id_strs  REGEX [[^ID="?([^"]+)"?]])
      file(STRINGS "/etc/os-release" _ver_strs REGEX [[^VERSION_ID="?([^"]+)"?]])
      string(REGEX REPLACE [[ID="?([^"]+)"?]]         [[\1]] _distro_id      "${_id_strs}")
      string(REGEX REPLACE [[VERSION_ID="?([^"]+)"?]] [[\1]] _distro_version "${_ver_strs}")

    # -- method 3: use lsb_release
    else()
      find_program(LSB_RELEASE_EXECUTABLE NAMES lsb_release lsb-release)
      if (LSB_RELEASE_EXECUTABLE)
        execute_process(
          COMMAND ${LSB_RELEASE_EXECUTABLE} --short --id
          OUTPUT_VARIABLE _distro_id
          OUTPUT_STRIP_TRAILING_WHITESPACE
        )
        execute_process(
          COMMAND ${LSB_RELEASE_EXECUTABLE} --short --release
          OUTPUT_VARIABLE _distro_version
          OUTPUT_STRIP_TRAILING_WHITESPACE
        )
      endif()
    endif()
  else()
    set(_system_os "${CMAKE_HOST_SYSTEM_NAME}")
  endif()

  # set 'system_id'
  if (_distro_id AND _distro_version)
    set(_system_id  "${_distro_id}-${_distro_version}")
  else()
    set(_system_id  "${_system_os}")
  endif()

  # convert to lowercase
  string(TOLOWER  "${_system_os}"       _system_os)
  string(TOLOWER  "${_distro_id}"       _distro_id)
  string(TOLOWER  "${_distro_version}"  _distro_version)
  string(TOLOWER  "${_system_id}"       _system_id)
  string(TOLOWER  "${_system_arch}"     _system_arch)

  # print
  message(STATUS "ty_query_host_system_info()")
  message(STATUS "  host_system_os     : ${_system_os}")
  message(STATUS "  host_distro_id     : ${_distro_id}")
  message(STATUS "  host_distro_version: ${_distro_version}")
  message(STATUS "  host_system_id     : ${_system_id}")
  message(STATUS "  host_system_arch   : ${_system_arch}")
  message(STATUS "ty_query_host_system_info() - success")

  # set in parent scope
  set(host_system_os       "${_system_os}"       PARENT_SCOPE)
  set(host_distro_id       "${_distro_id}"       PARENT_SCOPE)
  set(host_distro_version  "${_distro_version}"  PARENT_SCOPE)
  set(host_system_id       "${_system_id}"       PARENT_SCOPE)
  set(host_system_arch     "${_system_arch}"     PARENT_SCOPE)
endfunction()
