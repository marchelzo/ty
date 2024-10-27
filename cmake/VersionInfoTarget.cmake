#[=============================================================================[
MIT License

Copyright (c) 2024 Stephen Karavos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
#]=============================================================================]
#
# source: <https://github.com/skaravos/CMakeVersionInfoTarget>
#
cmake_minimum_required(VERSION 3.10)

#[=============================================================================[
  adds two cmake targets:
    1. a C/C++ static library target that contains project version info
    2. [internal] a cmake custom target that queries version info at build time

  add_version_info_target(NAME unique_target_name
                         [LINK_TO <target>...]
                         [NAMESPACE <namespace>...]
                         [LANGUAGE <language>]
                         [GIT_WORK_TREE <git_work_tree>]
                         [PROJECT_NAME <name>]
                         [PROJECT_VERSION <version>]
                        )

  NAME <unique_target_name>
    (required)
    provides the name of the static library target to create
    An alias target will also be created: 'VersionInfo::<unique_target_name>'

  LINK_TO <target> ...
    (optional)
    if provided, this library will be automatically linked to all given targets

  NAMESPACE <namespace> ...
    (optional; default="VersionInfo")
    if provided, the variables contained in the generated headers files will be
    enclosed in a namespace (C++) or have an underscore_separated prefix (C).
    NOTE: to disable the default namespace entirely and declare the variables
          in the global scope, you can provide an empty string as the namespace

      ex. (LANGUAGE=C++)
        # CMakeLists.txt
        add_version_info_target(NAME FooVersion NAMESPACE Abc XyZ LANGUAGE CXX)
        // 'VersionInfo.hpp'
        namespace Abc {
        namespace XyZ {
          extern const char* const ProjectName;
          ...
        }
        }

      ex. (LANGUAGE=C)
        # CMakeLists.txt
        add_version_info_target(NAME FooVersion NAMESPACE Abc XyZ LANGUAGE C)
        // 'VersionInfo.h'
        extern const char* const Abc_XyZ_ProjectName;
        ...

  LANGUAGE <language>
    (optional; default=CXX)
    specify the language used for the header and source files (C or CXX)

  GIT_WORK_TREE <git_work_tree> (optional)
    if provided, git commit information will be queried at build-time
    from the provided <git_work_tree>.
    NOTE: this option requires cmake to be able to find_package(Git)
    NOTE: if the git_work_tree is provided as a relative path it will be
          considered relative to the \${CMAKE_CURRENT_SOURCE_DIR}

  PROJECT_NAME <name>
    (optional; default=\${PROJECT_NAME})
    if provided, the generated library will contain the given project <name>
    instead of the current cmake project name taken from the \${PROJECT_NAME}
    cmake variable

  PROJECT_VERSION <version>
    (optional; default=\${PROJECT_VERSION})
    if provided, the given version string will be parsed into sub-components
    and inserted into the generated library.
    NOTE: the version string must match the form
          major[.minor[.patch[.tweak]]][-suffix]
    NOTE: leading zeroes in version components are preserved
    NOTE: the major, minor, patch and tweak versions must be numeric, but the
          optional suffix can contain any characters that aren't double-quotes,
          backslashes, percent signs, or whitespace.
          e.g. the following are all valid versions
            - 1
            - 1.2
            - 1.2.3
            - 1.2.3.4
            - 1.2.3.4-rc1
            - 1.2.3-alpha0
            - 1.2-beta#1
            - 1-derang3d_suff!x-with^-$pec;a|-c#@ra[ters

#]=============================================================================]
function(add_version_info_target)

  # --- functions for err messages

  function (__invalid_argument ARG_NAME)
    message(FATAL_ERROR "invalid argument: ${ARG_NAME}\n" ${ARGN})
  endfunction()

  function (__unknown_argument ARG_NAME)
    message(FATAL_ERROR "unknown argument: ${ARG_NAME}\n" ${ARGN})
  endfunction()

  function (__missing_argument ARG_NAME)
    message(FATAL_ERROR "missing argument: ${ARG_NAME}\n" ${ARGN})
  endfunction()

  # --- parse arguments

  set(_options)
  set(_singleargs NAME LANGUAGE GIT_WORK_TREE PROJECT_NAME PROJECT_VERSION)
  set(_multiargs LINK_TO NAMESPACE)
  cmake_parse_arguments(
    PARSE_ARGV 0
    arg
    "${_options}"
    "${_singleargs}"
    "${_multiargs}"
  )

  message(STATUS "add_version_info_target('${arg_NAME}')")

  foreach(_arg IN LISTS arg_UNPARSED_ARGUMENTS)
    __unknown_argument("${_arg}")
  endforeach()

  foreach(_arg IN LISTS arg_KEYWORDS_MISSING_VALUES)
    __invalid_argument("${_arg}" "cannot be provided without a value")
  endforeach()

  # --- validate arguments

  if (NOT arg_NAME)
    __missing_argument("NAME"
      "a unique name is always required for the version info target")
  endif()

  if (NOT arg_PROJECT_VERSION AND ("${PROJECT_VERSION}" STREQUAL ""))
    __missing_argument("PROJECT_VERSION"
      "is required because cmake variable \${PROJECT_VERSION} is not set")
  endif()

  if (TARGET ${arg_NAME})
    __invalid_argument("NAME" "provided value refers to a target that already exists [${arg_NAME}]")
  endif()

  foreach(_ns ${arg_NAMESPACE})
    if(NOT _ns MATCHES "^[_a-zA-Z][_a-zA-Z0-9]*$")
      __invalid_argument("NAMESPACE" "provided value isn't valid in C/C++ [${_ns}]")
    endif()
  endforeach()

  foreach(_tgt ${arg_LINK_TO})
    if (NOT TARGET ${_tgt})
      __invalid_argument("LINK_TO" "provided value isn't an existing cmake target [${_tgt}]")
    endif()
  endforeach()

  if (arg_GIT_WORK_TREE)
    get_filename_component(_git_work_tree "${arg_GIT_WORK_TREE}" ABSOLUTE
      BASE_DIR "${CMAKE_CURRENT_SOURCE_DIR}")
    if (NOT EXISTS "${_git_work_tree}")
      __invalid_argument("GIT_WORK_TREE" "provided directory does not exist [${arg_GIT_WORK_TREE}]")
    endif()
    find_package(Git REQUIRED QUIET)
    if (NOT GIT_EXECUTABLE)
      __invalid_argument("GIT_WORK_TREE" "'git' executable could not be found")
    endif()
    execute_process(
      COMMAND ${GIT_EXECUTABLE} rev-parse HEAD
      WORKING_DIRECTORY ${_git_work_tree}
      RESULT_VARIABLE _git_result
      OUTPUT_QUIET
      ERROR_QUIET
    )
    if (NOT _git_result EQUAL 0)
      __invalid_argument("GIT_WORK_TREE"
        "provided directory is not a git repository [${_git_work_tree}]")
    endif()
  endif()

  if (arg_LANGUAGE AND (NOT "${arg_LANGUAGE}" MATCHES [[^(C|CXX|C\+\+|CPP)$]]))
    __invalid_argument("LANGUAGE" "must be one of: C or CXX")
  endif()

  # --- determine language to use

  if (${arg_LANGUAGE} STREQUAL "C")
    if (NOT CMAKE_C_COMPILER)
      __invalid_argument("LANGUAGE" "C specified but no C compiler found")
    endif()
    set(_language "C")
    set(_hdr_ext  "h")
    set(_src_ext  "c")
  else()
    if (NOT CMAKE_CXX_COMPILER)
      __invalid_argument("LANGUAGE" "CXX specified but no CXX compiler found")
    endif()
    set(_language "CXX")
    set(_hdr_ext  "hpp")
    set(_src_ext  "cpp")
  endif()

  # --- set internal variables

  set(_vinfo_workspace "${CMAKE_CURRENT_BINARY_DIR}/${arg_NAME}")
  set(_vinfo_src       "${_vinfo_workspace}/VersionInfo.${_src_ext}")
  set(_vinfo_hdr       "${_vinfo_workspace}/include/${arg_NAME}/VersionInfo.${_hdr_ext}")

  set(_vinfo_templates_dir "${_vinfo_workspace}/templates")
  set(_vinfo_src_in    "${_vinfo_templates_dir}/VersionInfo.${_src_ext}.in")
  set(_vinfo_hdr_in    "${_vinfo_templates_dir}/VersionInfo.${_hdr_ext}.in")

  set(_vinfo_query_cmake "${_vinfo_workspace}/VersionInfoQuery.cmake")
  set(_query_targetname  "${arg_NAME}_QueryVersionInfo")

  # --- determine version to use

  if (arg_PROJECT_VERSION)
    set(_project_version ${arg_PROJECT_VERSION})
  else()
    set(_project_version ${PROJECT_VERSION})
  endif()

  set(_suffix_ch_set "^\n\t \%\"\\") # <-- no whitespace, percent, double-quote, or backslash
  if (NOT "${_project_version}" MATCHES
          "^([0-9]+)(\\.([0-9]+)(\\.([0-9]+)(\\.([0-9]+))?)?)?(-([${_suffix_ch_set}]+))?$")
    __invalid_argument("PROJECT_VERSION"
      "version must be of the form: ^major[.minor[.patch[.tweak]]][-suffix]$")
  endif()
  set(_version        "${CMAKE_MATCH_0}")
  set(_version_major  "${CMAKE_MATCH_1}")
  set(_version_minor  "${CMAKE_MATCH_3}")
  set(_version_patch  "${CMAKE_MATCH_5}")
  set(_version_tweak  "${CMAKE_MATCH_7}")
  set(_version_suffix "${CMAKE_MATCH_9}")

  # --- determine project name

  if (arg_PROJECT_NAME)
    set(_project_name "${arg_PROJECT_NAME}")
  else()
    set(_project_name "${PROJECT_NAME}")
  endif()

  # --- setup namespace variables for configuring Version.h.in

  if (DEFINED arg_NAMESPACE)
    set(_namespace ${arg_NAMESPACE})
  else()
    set(_namespace "VersionInfo") # default if user didnt give an explicit value
  endif()

  if (_namespace)
    # for the first given namespace
    list(POP_FRONT _namespace _ns1)
    set(_namespace_access_prefix "${_ns1}_")
    set(_namespace_scope_opening "namespace ${_ns1} {")
    set(_namespace_scope_closing "} /* namespace ${_ns1} */")
    set(_namespace_scope_resolve "${_ns1}::")

    # for each additional namespace in the argument list (if-any)
    foreach(_ns ${_namespace})
      set(_namespace_access_prefix "${_namespace_access_prefix}${_ns}_")
      set(_namespace_scope_opening "${_namespace_scope_opening}\nnamespace ${_ns} {")
      set(_namespace_scope_closing "${_namespace_scope_closing}\n} /* namespace ${_ns} */")
      set(_namespace_scope_resolve "${_namespace_scope_resolve}${_ns}::")
    endforeach()
  endif()

  # --- make some workspace directories

  file(MAKE_DIRECTORY "${_vinfo_workspace}")
  file(MAKE_DIRECTORY "${_vinfo_workspace}/include/${arg_NAME}")
  file(MAKE_DIRECTORY "${_vinfo_templates_dir}")

  # --- generate placeholder files

  # create VersionInfoQuery.cmake
  __create_vinfo_query_cmake(${_vinfo_query_cmake})

  # create header and source file templates (that will be configured at build)
  __create_vinfo_header_template(
    TEMPLATE_FILEPATH       "${_vinfo_hdr_in}"
    TARGET_NAME             "${arg_NAME}"
    LANGUAGE                "${_language}"
    NAMESPACE_ACCESS_PREFIX "${_namespace_access_prefix}"
    NAMESPACE_SCOPE_OPENING "${_namespace_scope_opening}"
    NAMESPACE_SCOPE_CLOSING "${_namespace_scope_closing}"
    GIT_WORK_TREE           "${_git_work_tree}"
  )
  __create_vinfo_source_template(
    TEMPLATE_FILEPATH       "${_vinfo_src_in}"
    TARGET_NAME             "${arg_NAME}"
    LANGUAGE                "${_language}"
    PROJECT_NAME            "${_project_name}"
    PROJECT_VERSION         "${_version}"
    PROJECT_VERSION_MAJOR   "${_version_major}"
    PROJECT_VERSION_MINOR   "${_version_minor}"
    PROJECT_VERSION_PATCH   "${_version_patch}"
    PROJECT_VERSION_TWEAK   "${_version_tweak}"
    PROJECT_VERSION_SUFFIX  "${_version_suffix}"
    NAMESPACE_ACCESS_PREFIX "${_namespace_access_prefix}"
    NAMESPACE_SCOPE_OPENING "${_namespace_scope_opening}"
    NAMESPACE_SCOPE_CLOSING "${_namespace_scope_closing}"
    NAMESPACE_SCOPE_RESOLVE "${_namespace_scope_resolve}"
    GIT_WORK_TREE           "${_git_work_tree}"
  )

  # we use file(APPEND ...) here to generate a temporary copies of the source
  # and header files to prevent CMake freaking out about 'file does not exist'
  # NOTE: when the custom QueryVersionInfo target is built, the Version.cmake
  #       script is invoked which will create the real copies of the files
  file(APPEND ${_vinfo_hdr} "")
  file(APPEND ${_vinfo_src} "")

  # --- create query target

  add_custom_target(${_query_targetname} ALL
    BYPRODUCTS
      ${_vinfo_hdr}
      ${_vinfo_src}
    COMMAND
      ${CMAKE_COMMAND}
      -D_VINFO_HDR_IN=${_vinfo_hdr_in}
      -D_VINFO_HDR=${_vinfo_hdr}
      -D_VINFO_SRC_IN=${_vinfo_src_in}
      -D_VINFO_SRC=${_vinfo_src}
      -D_GIT_WORK_TREE=${_git_work_tree}
      -D_BUILD_TYPE=$<CONFIG>
      -P ${_vinfo_query_cmake}
    COMMENT
      "Querying project version information and writing VersionInfo files..."
    DEPENDS
      ${_vinfo_hdr_in}
      ${_vinfo_src_in}
      ${_vinfo_query_cmake}
  )

  # --- create library target

  add_library(${arg_NAME} STATIC)
  add_library(VersionInfo::${arg_NAME} ALIAS ${arg_NAME})
  set_property(TARGET ${arg_NAME} PROPERTY C_STANDARD 99)
  set_property(TARGET ${arg_NAME} PROPERTY CXX_STANDARD 98)

  target_sources(${arg_NAME} PRIVATE ${_vinfo_hdr} ${_vinfo_src})

  target_include_directories(${arg_NAME}
    # NOTE: set both INTERFACE & PRIVATE here because PUBLIC isn't working???
    INTERFACE
      # including both level of include directories gives users a choice between
      #    #include "VersionInfo.h"
      #    #include "<TargetName>/VersionInfo.h"
      #
      "${_vinfo_workspace}/include"
      "${_vinfo_workspace}/include/${arg_NAME}"
    PRIVATE
      "${_vinfo_workspace}/include"
      "${_vinfo_workspace}/include/${arg_NAME}"
  )

  set_target_properties(${arg_NAME}
    PROPERTIES
      LINKER_LANGUAGE ${_language}
  )

  # gotta make sure it depends on the query target so that the query runs first!
  add_dependencies(${arg_NAME} ${_query_targetname})

  # --- link the target to any provided user targets

  foreach(_tgt ${arg_LINK_TO})
    message(STATUS "  privately linking target ${_tgt} to ${arg_NAME}")
    target_link_libraries(${_tgt} PRIVATE ${arg_NAME})
  endforeach()

  # --- done!

  message(STATUS "add_version_info_target('${arg_NAME}') - success")

endfunction()

#[=============================================================================[
                            INTERNAL FUNCTION
#]=============================================================================]
function(__create_vinfo_header_template)
  # --- parse arguments

  set(_singleargs
    TARGET_NAME
    TEMPLATE_FILEPATH        # absolute path to generated header file
    LANGUAGE                 # "C" or "CXX"
    NAMESPACE_ACCESS_PREFIX  # variable prefix   (only used in C)
    NAMESPACE_SCOPE_OPENING  # namespace opening (only used in C++)
    NAMESPACE_SCOPE_CLOSING  # namespace closing (only used in C++)
    GIT_WORK_TREE            # if-defined, insert git related variables
  )
  cmake_parse_arguments(PARSE_ARGV 0 arg "" "${_singleargs}" "")

  # if the given arguments haven't changed since the last call, do nothing
  string(SHA256 _argn_hash "${ARGN}")
  string(MAKE_C_IDENTIFIER "${arg_TARGET_NAME}" _tn)
  if ("${_argn_hash}" STREQUAL "${_CREATE_VINFO_HEADER_TEMPLATE_LASTHASH_${_tn}}")
    return()
  endif()

  # --- setup language-specific template features

  if ("${arg_LANGUAGE}" STREQUAL "C")
    set(_namespace_prefix  ${arg_NAMESPACE_ACCESS_PREFIX})
    set(_namespace_opening)
    set(_namespace_closing)
  else()
    set(_namespace_prefix)
    set(_namespace_opening ${arg_NAMESPACE_SCOPE_OPENING})
    set(_namespace_closing ${arg_NAMESPACE_SCOPE_CLOSING})
  endif()

  # --- setup git-specific template variables

  if (_git_work_tree)
    if ("${arg_LANGUAGE}" STREQUAL "C")
      set(_git_var_uncommittedchanges
          "extern const int         ${_namespace_prefix}GitUncommittedChanges; // 0 - false, 1 - true")
    else()
      set(_git_var_uncommittedchanges
          "extern const bool        GitUncommittedChanges;")
    endif()
    set(_git_var_gitcommithash   "extern const char* const ${_namespace_prefix}GitCommitHash;")
    set(_git_var_gitcommitdate   "extern const char* const ${_namespace_prefix}GitCommitDate;")
    set(_git_var_gitusername     "extern const char* const ${_namespace_prefix}GitUserName;")
    set(_git_var_gituseremail    "extern const char* const ${_namespace_prefix}GitUserEmail;")
    set(_git_var_gitauthorname   "extern const char* const ${_namespace_prefix}GitAuthorName;")
    set(_git_var_gitauthoremail  "extern const char* const ${_namespace_prefix}GitAuthorEmail;")
  endif()

  # --- write the template file

  file(WRITE "${arg_TEMPLATE_FILEPATH}" "
/* This file is auto-generated by VersionInfoTarget.cmake, do not edit. */
#pragma once

${_namespace_opening}
extern const char* const ${_namespace_prefix}ProjectName;
extern const char* const ${_namespace_prefix}ProjectVersion;
extern const char* const ${_namespace_prefix}ProjectVersionMajor;
extern const char* const ${_namespace_prefix}ProjectVersionMinor;
extern const char* const ${_namespace_prefix}ProjectVersionPatch;
extern const char* const ${_namespace_prefix}ProjectVersionTweak;
extern const char* const ${_namespace_prefix}ProjectVersionSuffix;
extern const char* const ${_namespace_prefix}CompilerId;
extern const char* const ${_namespace_prefix}CompilerVersion;
extern const char* const ${_namespace_prefix}Architecture; // x86  x64
extern const char* const ${_namespace_prefix}BuildType;    // debug  release
extern const char* const ${_namespace_prefix}VersionSummary;
extern const char* const ${_namespace_prefix}VersionSummaryDetailed;
${_git_var_uncommittedchanges}
${_git_var_gitcommithash}
${_git_var_gitcommitdate}
${_git_var_gitusername}
${_git_var_gituseremail}
${_git_var_gitauthorname}
${_git_var_gitauthoremail}
${_namespace_closing}
"
) # end file(WRITE "${arg_TEMPLATE_FILEPATH}"...

  set(_CREATE_VINFO_HEADER_TEMPLATE_LASTHASH_${_tn} "${_argn_hash}" CACHE INTERNAL "")

endfunction() # __create_vinfo_header_template

#[=============================================================================[
                            INTERNAL FUNCTION
#]=============================================================================]
function(__create_vinfo_source_template)

  # --- parse arguments

  set(_singleargs
    TARGET_NAME
    TEMPLATE_FILEPATH       # absolute path to generated header file
    LANGUAGE                # "C" or "CXX"
    PROJECT_NAME            # self-explanatory
    PROJECT_VERSION         # self-explanatory
    PROJECT_VERSION_MAJOR   # self-explanatory
    PROJECT_VERSION_MINOR   # self-explanatory
    PROJECT_VERSION_PATCH   # self-explanatory
    PROJECT_VERSION_TWEAK   # self-explanatory
    PROJECT_VERSION_SUFFIX  # self-explanatory
    NAMESPACE_ACCESS_PREFIX # self-explanatory (only used in C)
    NAMESPACE_SCOPE_OPENING # self-explanatory (only used in C++)
    NAMESPACE_SCOPE_CLOSING # self-explanatory (only used in C++)
    NAMESPACE_SCOPE_RESOLVE # self-explanatory (only used in C++)
    GIT_WORK_TREE           # if-defined, insert git related variables
  )
  cmake_parse_arguments(PARSE_ARGV 0 arg "" "${_singleargs}" "")

  # if the given arguments haven't changed since the last call, do nothing
  string(SHA256 _argn_hash "${ARGN}")
  string(MAKE_C_IDENTIFIER "${arg_TARGET_NAME}" _tn)
  if ("${_argn_hash}" STREQUAL "${_CREATE_VINFO_SOURCE_TEMPLATE_LASTHASH_${_tn}}")
    return()
  endif()

  # --- setup language-specific template features

  if ("${arg_LANGUAGE}" STREQUAL "C")
    set(_namespace_prefix  ${arg_NAMESPACE_ACCESS_PREFIX})
    set(_namespace_opening)
    set(_namespace_closing)
    set(_extension "h")
    set(_compiler_id      ${CMAKE_C_COMPILER_ID})
    set(_compiler_version ${CMAKE_C_COMPILER_VERSION})
  else()
    set(_namespace_prefix)
    set(_namespace_opening ${arg_NAMESPACE_SCOPE_OPENING})
    set(_namespace_closing ${arg_NAMESPACE_SCOPE_CLOSING})
    set(_extension "hpp")
    set(_compiler_id      ${CMAKE_CXX_COMPILER_ID})
    set(_compiler_version ${CMAKE_CXX_COMPILER_VERSION})
  endif()

  # --- setup git-specific template variables

  if (arg_GIT_WORK_TREE)
    if ("${arg_LANGUAGE}" STREQUAL "C")
      set(_git_var_uncommittedchanges
          "const int ${_namespace_prefix}GitUncommittedChanges  = @_GIT_UNCOMMITTED_CHANGES@;")
    else()
      set(_git_var_uncommittedchanges
          "const bool GitUncommittedChanges = static_cast<bool>(@_GIT_UNCOMMITTED_CHANGES@);")
    endif()
    set(_git_var_gitcommithash  "const char* const ${_namespace_prefix}GitCommitHash  = \"@_GIT_COMMIT_HASH@\";")
    set(_git_var_gitcommitdate  "const char* const ${_namespace_prefix}GitCommitDate  = \"@_GIT_COMMIT_DATE@\";")
    set(_git_var_gitusername    "const char* const ${_namespace_prefix}GitUserName    = \"@_GIT_USER_NAME@\";")
    set(_git_var_gituseremail   "const char* const ${_namespace_prefix}GitUserEmail   = \"@_GIT_USER_EMAIL@\";")
    set(_git_var_gitauthorname  "const char* const ${_namespace_prefix}GitAuthorName  = \"@_GIT_AUTHOR_NAME@\";")
    set(_git_var_gitauthoremail "const char* const ${_namespace_prefix}GitAuthorEmail = \"@_GIT_AUTHOR_EMAIL@\";")
    set(_git_str_constant_hash "\"\\nCommitHash: @_GIT_COMMIT_HASH@@_GIT_UNCOMMITTED_CHANGES_STRING@\"")
    set(_git_str_constant_user "\"\\nCommitUser: @_GIT_USER_NAME@ (@_GIT_USER_EMAIL@)\"")
    set(_git_str_constant_date "\"\\nCommitDate: @_GIT_COMMIT_DATE@\"")
    set(_git_str_constant_equals_githaduncommitted "\"\\nGitHadUncommittedChanges='@_GIT_UNCOMMITTED_CHANGES@'\"")
    set(_git_str_constant_equals_gitcommithash     "\"\\nGitCommitHash='@_GIT_COMMIT_HASH@'\"")
    set(_git_str_constant_equals_gitcommitdate     "\"\\nGitCommitDate='@_GIT_COMMIT_DATE@'\"")
    set(_git_str_constant_equals_gitusername       "\"\\nGitUserName='@_GIT_USER_NAME@'\"")
    set(_git_str_constant_equals_gituseremail      "\"\\nGitUserEmail='@_GIT_USER_EMAIL@'\"")
    set(_git_str_constant_equals_gitauthorname     "\"\\nGitAuthorName='@_GIT_AUTHOR_NAME@'\"")
    set(_git_str_constant_equals_gitauthoremail    "\"\\nGitAuthorEmail='@_GIT_AUTHOR_EMAIL@'\"")
  endif()

  file(WRITE "${arg_TEMPLATE_FILEPATH}" "
/* This file is auto-generated by VersionInfoTarget.cmake, do not edit. */
#include \"${arg_TARGET_NAME}/VersionInfo.${_extension}\"

${_namespace_opening}
const char* const ${_namespace_prefix}ProjectName          = \"${arg_PROJECT_NAME}\";
const char* const ${_namespace_prefix}ProjectVersion       = \"${arg_PROJECT_VERSION}\";
const char* const ${_namespace_prefix}ProjectVersionMajor  = \"${arg_PROJECT_VERSION_MAJOR}\";
const char* const ${_namespace_prefix}ProjectVersionMinor  = \"${arg_PROJECT_VERSION_MINOR}\";
const char* const ${_namespace_prefix}ProjectVersionPatch  = \"${arg_PROJECT_VERSION_PATCH}\";
const char* const ${_namespace_prefix}ProjectVersionTweak  = \"${arg_PROJECT_VERSION_TWEAK}\";
const char* const ${_namespace_prefix}ProjectVersionSuffix = \"${arg_PROJECT_VERSION_SUFFIX}\";
const char* const ${_namespace_prefix}CompilerId           = \"${_compiler_id}\";
const char* const ${_namespace_prefix}CompilerVersion      = \"${_compiler_version}\";
const char* const ${_namespace_prefix}Architecture         = \"${CMAKE_SYSTEM_PROCESSOR}\";
const char* const ${_namespace_prefix}BuildType            = \"@_BUILD_TYPE@\";

${_git_var_uncommittedchanges}
${_git_var_gitcommithash}
${_git_var_gitcommitdate}
${_git_var_gitusername}
${_git_var_gituseremail}
${_git_var_gitauthorname}
${_git_var_gitauthoremail}

const char* const ${_namespace_prefix}VersionSummary =
\"Project: ${arg_PROJECT_NAME}\"
\"\\nVersion: ${arg_PROJECT_VERSION}\"
\"\\nCompiler: ${_compiler_id}-${_compiler_version}\"
\"\\nPlatform: ${CMAKE_SYSTEM_PROCESSOR}@_BUILD_TYPE_SUFFIX@\"
${_git_str_constant_hash}
${_git_str_constant_user}
${_git_str_constant_date}
;

const char* const ${_namespace_prefix}VersionSummaryDetailed =
\"ProjectName='${arg_PROJECT_NAME}'\"
\"\\nProjectVersion='${arg_PROJECT_VERSION}'\"
\"\\nProjectVersionMajor='${arg_PROJECT_VERSION_MAJOR}'\"
\"\\nProjectVersionMinor='${arg_PROJECT_VERSION_MINOR}'\"
\"\\nProjectVersionPatch='${arg_PROJECT_VERSION_PATCH}'\"
\"\\nProjectVersionTweak='${arg_PROJECT_VERSION_TWEAK}'\"
\"\\nProjectVersionSuffix='${arg_PROJECT_VERSION_SUFFIX}'\"
\"\\nCompilerId='${_compiler_id}'\"
\"\\nCompilerVersion='${_compiler_version}'\"
\"\\nArchitecture='${CMAKE_SYSTEM_PROCESSOR}'\"
\"\\nBuildType='@_BUILD_TYPE@'\"
${_git_str_constant_equals_githaduncommitted}
${_git_str_constant_equals_gitcommithash}
${_git_str_constant_equals_gitcommitdate}
${_git_str_constant_equals_gitusername}
${_git_str_constant_equals_gituseremail}
${_git_str_constant_equals_gitauthorname}
${_git_str_constant_equals_gitauthoremail}
;

${_namespace_closing}
"
) # end file(WRITE "${arg_TEMPLATE_FILEPATH}"...

  set(_CREATE_VINFO_SOURCE_TEMPLATE_LASTHASH_${_tn} "${_argn_hash}" CACHE INTERNAL "")

endfunction() # __create_vinfo_source_template

#[=============================================================================[
                            INTERNAL FUNCTION
#]=============================================================================]
function(__create_vinfo_query_cmake arg_TARGET_FILEPATH)
  if (EXISTS "${arg_TARGET_FILEPATH}")
    return()
  endif()
  file(WRITE ${arg_TARGET_FILEPATH} [==========[
# This file is auto-generated by VersionInfoTarget.cmake, do not edit.

# This file configures the VersionInfo header and source files with build-time
# information relating to the current build (debug, release, etc.)
#
# It also uses the git executable to determine relevant repository info:
#   Dirty Status, Commit Date, Commit Hash, Commit User Name, Commit User Email,
#   Commit Author Name, Commit Author Email
#
# This module is NOT designed to be directly included in a CMakeLists.txt file.
#
# It should be called as a COMMAND in a custom_target.
# Because the information is inserted into the Version header at the time this
# file is parsed, the goal is to have this file be parsed right before the main
# program executable is compiled. Calling this file from a custom_target ensures
# that we can configure the dependencies so that it gets run at compile time

if (_GIT_WORK_TREE)
  find_package(Git REQUIRED QUIET)
  # --- Git Status (is it dirty?)
  execute_process(
    COMMAND ${GIT_EXECUTABLE} status --porcelain --untracked-files=no
    WORKING_DIRECTORY ${_GIT_WORK_TREE}
    OUTPUT_VARIABLE _git_status_output
  )
  if (_git_status_output)
    set(_GIT_UNCOMMITTED_CHANGES "1")
    set(_GIT_UNCOMMITTED_CHANGES_STRING " (uncommitted changes)")
    message(WARNING
    "\nGit repository is dirty (uncommitted changes); do not release this version"
    )
  else()
    set(_GIT_UNCOMMITTED_CHANGES "0")
    set(_GIT_UNCOMMITTED_CHANGES_STRING)
  endif()
  # --- Git Revision Hash
  execute_process(
    COMMAND ${GIT_EXECUTABLE} rev-parse HEAD
    WORKING_DIRECTORY ${_GIT_WORK_TREE}
    OUTPUT_VARIABLE _GIT_COMMIT_HASH
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  # --- Git Commit Date
  execute_process(
    COMMAND ${GIT_EXECUTABLE} show -s --format=%cd HEAD
    WORKING_DIRECTORY ${_GIT_WORK_TREE}
    OUTPUT_VARIABLE _GIT_COMMIT_DATE
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  # --- Git User Name
  execute_process(
    COMMAND ${GIT_EXECUTABLE} show -s --format=%cn
    WORKING_DIRECTORY ${_GIT_WORK_TREE}
    OUTPUT_VARIABLE _GIT_USER_NAME
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  # --- Git User Email
  execute_process(
    COMMAND ${GIT_EXECUTABLE} show -s --format=%ce
    WORKING_DIRECTORY ${_GIT_WORK_TREE}
    OUTPUT_VARIABLE _GIT_USER_EMAIL
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  # --- Git Author Name
  execute_process(
    COMMAND ${GIT_EXECUTABLE} show -s --format=%an
    WORKING_DIRECTORY ${_GIT_WORK_TREE}
    OUTPUT_VARIABLE _GIT_AUTHOR_NAME
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  # --- Git Author Email
  execute_process(
    COMMAND ${GIT_EXECUTABLE} show -s --format=%ae
    WORKING_DIRECTORY ${_GIT_WORK_TREE}
    OUTPUT_VARIABLE _GIT_AUTHOR_EMAIL
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
endif(_GIT_WORK_TREE)

# --- C++ specific features

if (_BUILD_TYPE)
  set(_BUILD_TYPE_SUFFIX "-${_BUILD_TYPE}")
endif()

# --- Configure Version header

configure_file(
  ${_VINFO_HDR_IN}
  ${_VINFO_HDR}
  @ONLY
)

# --- Configure Version header

configure_file(
  ${_VINFO_SRC_IN}
  ${_VINFO_SRC}
  @ONLY
)
]==========]
  )
endfunction() # __create_vinfo_query_cmake
