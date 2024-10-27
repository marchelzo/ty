message(STATUS "CPackSetup")
list(APPEND CMAKE_MESSAGE_INDENT "  ")

# ---
#  collect system info
# ---

include(${PROJECT_SOURCE_DIR}/cmake/SystemUtils.cmake)
ty_query_host_system_info()

# ---
#   build date YYYY-MM-DD
# ---

string(TIMESTAMP _date "%Y-%m-%d")

# ------------------------------------------------
# --- set default generator
# ------------------------------------------------

list(APPEND CPACK_GENERATOR ZIP)

# ------------------------------------------------
# --- set cpack package variables
# ------------------------------------------------

set(CPACK_MONOLITHIC_INSTALL OFF)
set(CPACK_STRIP_FILES ON)

set(CPACK_PACKAGE_NAME "${PROJECT_NAME}")
set(CPACK_PACKAGE_ICON "")
set(CPACK_PACKAGE_VENDOR "Brad Garagan")
set(CPACK_PACKAGE_CONTACT "Brad Garagan <bradgaragan@gmail.com>")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "")
if (EXISTS "${PROJECT_SOURCE_DIR}/README.md")
  set(CPACK_PACKAGE_DESCRIPTION_FILE "${PROJECT_SOURCE_DIR}/README.md")
elseif (EXISTS "${PROJECT_SOURCE_DIR}/README.txt")
  set(CPACK_PACKAGE_DESCRIPTION_FILE "${PROJECT_SOURCE_DIR}/README.txt")
elseif (EXISTS "${PROJECT_SOURCE_DIR}/README")
  set(CPACK_PACKAGE_DESCRIPTION_FILE "${PROJECT_SOURCE_DIR}/README")
endif()
if (EXISTS "${PROJECT_SOURCE_DIR}/LICENSE.txt")
  set(CPACK_RESOURCE_FILE_LICENSE "${PROJECT_SOURCE_DIR}/LICENSE.txt")
elseif (EXISTS "${PROJECT_SOURCE_DIR}/LICENSE")
  set(CPACK_RESOURCE_FILE_LICENSE "${PROJECT_SOURCE_DIR}/LICENSE")
endif()
if (DEFINED PROJECT_VERSION)
  set(CPACK_PACKAGE_FILE_NAME "${CPACK_PACKAGE_NAME}-v${PROJECT_VERSION}-${host_system_id}-${host_system_arch}_${_date}")
  set(CPACK_PACKAGE_INSTALL_DIRECTORY "${CPACK_PACKAGE_NAME}-${PROJECT_VERSION}")
else()
  set(CPACK_PACKAGE_FILE_NAME "${CPACK_PACKAGE_NAME}-${host_system_id}-${host_system_arch}_${_date}")
  set(CPACK_PACKAGE_INSTALL_DIRECTORY "${CPACK_PACKAGE_NAME}")
endif()

# ------------------------------------------------
# --- add components
# ------------------------------------------------

include(CPackComponent)

# main executable
string(CONCAT _description
  "This component installs the main ty executable & required .ty modules"
)
cpack_add_component(InstallComponentTy
  DISPLAY_NAME "Ty executable & modules"
  DESCRIPTION ${_description}
  REQUIRED
)

# license
cpack_add_component(InstallComponentLicenseFile
  HIDDEN # dont let the user disable it
)

# ------------------------------------------------
# --- set a default package directory
# ------------------------------------------------

# NOTE: CPACK_PACKAGE_DIRECTORY sets the location for where packages are
#       generated. By default we want this to be <project-dir>/_packages
if(NOT CPACK_PACKAGE_DIRECTORY)
  # Get the relative path from the _build/ dir (i.e. ty/msvc2022)
  file(RELATIVE_PATH _rel_path_to_bin ${CMAKE_SOURCE_DIR}/_build ${CMAKE_BINARY_DIR})
  set(_cpack_default_packagedir "${CMAKE_SOURCE_DIR}/_packages/${_rel_path_to_bin}")
  # Expose the CPACK_PACKAGE_DIRECTORY as a cache variable so the user can override the default
  set(CPACK_PACKAGE_DIRECTORY ${_cpack_default_packagedir} CACHE PATH
      "Where to generate CPack installer packages")
endif()

# NOTE: package dir must always contain only unix-style paths
string(REPLACE "\\" "/" CPACK_PACKAGE_DIRECTORY "${CPACK_PACKAGE_DIRECTORY}" )

# ------------------------------------------------
# -- include the CPack module
# ------------------------------------------------

# NOTE: This must be called at the very end so that it inherits the current
#       value of all the variables that were set above.
include(CPack)

list(POP_BACK CMAKE_MESSAGE_INDENT)
message(STATUS "CPackSetup - success")
