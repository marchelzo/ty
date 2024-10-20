cmake_minimum_required(VERSION 3.10)

#[=============================================================================[
  adds two cmake targets:
    1. a C/C++ static library target that contains project version info
    2. [internal] a cmake custom target that queries version info at build time

  add_version_info_target(NAME <unique_target_name>
                         [LINK_TO targets...]
                         [NAMESPACE namespaces...]
                         [LANGUAGE language]
                         [GIT_WORK_TREE <git_work_tree>]
                         [PROJECT_NAME <name>]
                         [PROJECT_VERSION <version>]
                        )

  NAME <unique_target_name>  (required)
    provides the name of the static library target to create
    An alias target will also be created: 'VersionInfo::<unique_target_name>'

  LINK_TO targets... (optional)
    if provided, this library will be automatically linked to all given targets

  NAMESPACE namespaces... (optional; default="VersionInfo")
    if provided, the variables contained in the generated headers files will be
    enclosed in a namespace (C++) or have an underscore_separated prefix (C).

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

  LANGUAGE language (optional;default=CXX)
    specify the language used for the header and source files (C or CXX)

  GIT_WORK_TREE (optional)
    if provided, git commit information will be queried at build-time
    NOTE: this option requires cmake to be able to find_package(Git)

  PROJECT_NAME <name>  (optional; default=name of current project)
    if provided, the target will use the given name instead of the current
    project name.

  PROJECT_VERSION <version>  (optional; default=version of current project)
    if provided, the target will use the given version instead of the current
    project version.
    NOTE: must be provided in the form <major[.minor[.patch[[.-]tweak]]>
    NOTE: the 'tweak' version can be separated using either a period or a hyphen
          e.g. both 1.0.1.1 and 1.0.1-rev1 are valid versions

#]=============================================================================]
function(add_version_info_target)

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
    message(WARNING "Unparsed argument: ${_arg}")
  endforeach()

  # --- validate arguments

  if (NOT arg_NAME)
    message(FATAL_ERROR "NAME parameter is required")
  endif()

  if (TARGET ${arg_NAME})
    message(WARNING "A target with this NAME[${arg_NAME}] already exists")
  endif()

  foreach(_ns ${arg_NAMESPACE})
    if(NOT _ns MATCHES "^[_a-zA-Z][_a-zA-Z0-9]*$")
      message(FATAL_ERROR "Provided NAMESPACE [${_ns}] isn't valid in C/C++")
    endif()
  endforeach()

  foreach(_tgt ${arg_LINK_TO})
    if (NOT TARGET ${_tgt})
      message(FATAL_ERROR "LINK_TO parameter invalid: [${_tgt}] isn't a target")
    endif()
  endforeach()

  if (arg_GIT_WORK_TREE)
    if (NOT EXISTS "${arg_GIT_WORK_TREE}")
      message(FATAL_ERROR "Provided GIT_WORK_TREE does not exist")
    endif()
    find_package(Git REQUIRED QUIET)
    if (NOT GIT_EXECUTABLE)
      message(FATAL_ERROR "Parameter GIT_WORK_TREE provided but Git not found")
    endif()
    execute_process(
      COMMAND ${GIT_EXECUTABLE} rev-parse HEAD
      WORKING_DIRECTORY ${arg_GIT_WORK_TREE}
      RESULT_VARIABLE _git_result
      OUTPUT_QUIET
      ERROR_QUIET
    )
    if (NOT _git_result EQUAL 0)
      message(FATAL_ERROR "Provided GIT_WORK_TREE is not a git repository")
    endif()
  endif()

  if (arg_LANGUAGE AND (NOT "${arg_LANGUAGE}" MATCHES [[^(C|CXX|C\+\+)$]]))
    message(FATAL_ERROR "Parameter LANGUAGE must be one of: C or CXX")
  endif()

  # --- determine language to use

  if (${arg_LANGUAGE} STREQUAL "C")
    if (NOT CMAKE_C_COMPILER)
      message(FATAL_ERROR "LANGUAGE C specified but no C compiler found")
    endif()
    set(_language "C")
    set(_hdr_ext  "h")
    set(_src_ext  "c")
  else()
    if (NOT CMAKE_CXX_COMPILER)
      message(FATAL_ERROR "LANGUAGE CXX specified but no CXX compiler found")
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
    string(REGEX MATCH [[([0-9]+)(\.([0-9]+)(\.([0-9]+)([.-]([A-Za-z0-9]+))?)?)?]]
           _matched "${arg_PROJECT_VERSION}")
    set(_version       "${CMAKE_MATCH_0}")
    set(_version_major "${CMAKE_MATCH_1}")
    set(_version_minor "${CMAKE_MATCH_3}")
    set(_version_patch "${CMAKE_MATCH_5}")
    set(_version_tweak "${CMAKE_MATCH_7}")
  else()
    set(_version       ${PROJECT_VERSION})
    set(_version_major ${PROJECT_VERSION_MAJOR})
    set(_version_minor ${PROJECT_VERSION_MINOR})
    set(_version_patch ${PROJECT_VERSION_PATCH})
    set(_version_tweak ${PROJECT_VERSION_TWEAK})
  endif()

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
    TEMPLATE_FILEPATH       ${_vinfo_hdr_in}
    TARGET_NAME             ${arg_NAME}
    LANGUAGE                ${_language}
    NAMESPACE_ACCESS_PREFIX ${_namespace_access_prefix}
    NAMESPACE_SCOPE_OPENING ${_namespace_scope_opening}
    NAMESPACE_SCOPE_CLOSING ${_namespace_scope_closing}
    GIT_WORK_TREE           ${arg_GIT_WORK_TREE}
  )
  __create_vinfo_source_template(
    TEMPLATE_FILEPATH       ${_vinfo_src_in}
    TARGET_NAME             ${arg_NAME}
    LANGUAGE                ${_language}
    PROJECT_NAME            ${_project_name}
    PROJECT_VERSION         ${_version}
    PROJECT_VERSION_MAJOR   ${_version_major}
    PROJECT_VERSION_MINOR   ${_version_minor}
    PROJECT_VERSION_PATCH   ${_version_patch}
    PROJECT_VERSION_TWEAK   ${_version_tweak}
    NAMESPACE_ACCESS_PREFIX ${_namespace_access_prefix}
    NAMESPACE_SCOPE_OPENING ${_namespace_scope_opening}
    NAMESPACE_SCOPE_CLOSING ${_namespace_scope_closing}
    NAMESPACE_SCOPE_RESOLVE ${_namespace_scope_resolve}
    GIT_WORK_TREE           ${arg_GIT_WORK_TREE}
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
      -D_GIT_WORK_TREE=${arg_GIT_WORK_TREE}
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

  # extract TARGET_NAME from argument list
  cmake_parse_arguments(PARSE_ARGV 0 arg "" "TARGET_NAME" "")

  # if the given arguments haven't changed since the last call, do nothing
  string(SHA256 _argn_hash "${ARGN}")
  string(MAKE_C_IDENTIFIER "${arg_TARGET_NAME}" _tn)
  if ("${_argn_hash}" STREQUAL "${_CREATE_VINFO_HEADER_TEMPLATE_LASTHASH_${_tn}}")
    return()
  endif()

  # --- parse arguments

  set(_singleargs
    TEMPLATE_FILEPATH        # absolute path to generated header file
    LANGUAGE                 # "C" or "CXX"
    NAMESPACE_ACCESS_PREFIX  # variable prefix   (only used in C)
    NAMESPACE_SCOPE_OPENING  # namespace opening (only used in C++)
    NAMESPACE_SCOPE_CLOSING  # namespace closing (only used in C++)
    GIT_WORK_TREE            # if-defined, insert git related variables
  )
  cmake_parse_arguments(arg "" "${_singleargs}" "" ${arg_UNPARSED_ARGUMENTS})

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

  if (arg_GIT_WORK_TREE)
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

  # extract TARGET_NAME from argument list
  cmake_parse_arguments(PARSE_ARGV 0 arg "" "TARGET_NAME" "")

  # if the given arguments haven't changed since the last call, do nothing
  string(SHA256 _argn_hash "${ARGN}")
  string(MAKE_C_IDENTIFIER "${arg_TARGET_NAME}" _tn)
  if ("${_argn_hash}" STREQUAL "${_CREATE_VINFO_SOURCE_TEMPLATE_LASTHASH_${_tn}}")
    return()
  endif()

  # --- parse arguments

  set(_singleargs
    TEMPLATE_FILEPATH       # absolute path to generated header file
    LANGUAGE                # "C" or "CXX"
    PROJECT_NAME            # self-explanatory
    PROJECT_VERSION         # self-explanatory
    PROJECT_VERSION_MAJOR   # self-explanatory
    PROJECT_VERSION_MINOR   # self-explanatory
    PROJECT_VERSION_PATCH   # self-explanatory
    PROJECT_VERSION_TWEAK   # self-explanatory
    NAMESPACE_ACCESS_PREFIX # self-explanatory (only used in C)
    NAMESPACE_SCOPE_OPENING # self-explanatory (only used in C++)
    NAMESPACE_SCOPE_CLOSING # self-explanatory (only used in C++)
    NAMESPACE_SCOPE_RESOLVE # self-explanatory (only used in C++)
    GIT_WORK_TREE           # if-defined, insert git related variables
  )
  cmake_parse_arguments(arg "" "${_singleargs}" "" ${arg_UNPARSED_ARGUMENTS})

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
const char* const ${_namespace_prefix}ProjectName         = \"${arg_PROJECT_NAME}\";
const char* const ${_namespace_prefix}ProjectVersion      = \"${arg_PROJECT_VERSION}\";
const char* const ${_namespace_prefix}ProjectVersionMajor = \"${arg_PROJECT_VERSION_MAJOR}\";
const char* const ${_namespace_prefix}ProjectVersionMinor = \"${arg_PROJECT_VERSION_MINOR}\";
const char* const ${_namespace_prefix}ProjectVersionPatch = \"${arg_PROJECT_VERSION_PATCH}\";
const char* const ${_namespace_prefix}ProjectVersionTweak = \"${arg_PROJECT_VERSION_TWEAK}\";
const char* const ${_namespace_prefix}CompilerId          = \"${_compiler_id}\";
const char* const ${_namespace_prefix}CompilerVersion     = \"${_compiler_version}\";
const char* const ${_namespace_prefix}Architecture        = \"${CMAKE_SYSTEM_PROCESSOR}\";
const char* const ${_namespace_prefix}BuildType           = \"@_BUILD_TYPE@\";

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
