#!/usr/bin/env bash

set -ueo pipefail

_script_dir=$(readlink -f "$(dirname "$0")")
_project_dir=$(readlink -f "${_script_dir}/..")

function __print_usage_text() {
  >&2 cat <<EOF

  USAGE: $(basename "$0") [OPTIONS] <DOCKER_IMAGE> <OUTDIR_SUFFIX>

    Builds the project inside a specified DOCKER_IMAGE.

    This script mounts the project directory inside the container and
    sets the cmake build & cmake install dir to the following locations:

      - <project-dir>/_build/docker-<OUTDIR_SUFFIX>
      - <project-dir>/_install/docker-<OUTDIR_SUFFIX>

  OPTIONS
    -h --help          show this usage text
    -f --fresh         deletes the 'build' and 'install' directories (if-present)
                       before running the docker compilation

EOF
}

function __print_errormsg() {
  local esc=$'\033'
  local color_red="${esc}[0;31m"
  local color_reset="${esc}[00m"
  >&2 echo -e "\n${color_red}error: ${1}${color_reset}\n"
}

# ---
#  parse arguments
# ---

_opt_fresh=0
_arg_docker_image=
_arg_outdir_suffix=

while [[ "$#" -gt 0 ]]
do
  case "$1" in
    -h|--help)
      __print_usage_text
      exit 0
      ;;
    -f|--fresh)
      _opt_fresh=1 ;;
    -*)
      __print_errormsg "unknown option [$1]"
      __print_usage_text
      exit 1
      ;;
    *)
      if [[ -z "${_arg_docker_image}" ]]; then
        _arg_docker_image=$1
      elif [[ -z "${_arg_outdir_suffix}" ]]; then
        _arg_outdir_suffix=$1
      else
        __print_errormsg "too many arguments"
        __print_usage_text
        exit 1
      fi
      ;;
  esac
  shift
done

if [[ -z "$_arg_docker_image" ]]; then
  __print_errormsg "missing required arg <DOCKER_IMAGE>"
  __print_usage_text
  exit 1
fi

if [[ -z "$_arg_outdir_suffix" ]]; then
  __print_errormsg "missing required arg <OUTDIR_SUFFIX>"
  __print_usage_text
  exit 1
fi

echo "_opt_fresh[$_opt_fresh]"
echo "_arg_docker_image[$_arg_docker_image]"
echo "_arg_outdir_suffix[$_arg_outdir_suffix]"

# ---
#  set vars used for docker build
# ---

_uid=$(id -u "$(whoami)")
_guid=$(id -g "$(whoami)")
_build_dir="_build/docker-${_arg_outdir_suffix:?}"
_install_dir="_install/docker-${_arg_outdir_suffix:?}"

# ---
#  rm existing build & install dirs
# ---

if [ "${_opt_fresh}" -ne 0 ]; then
  if [ -d "${_project_dir:?}/${_build_dir:?}" ]; then
    rm -rv "${_project_dir:?}/${_build_dir:?}"
  fi
  if [ -d "${_project_dir:?}/${_install_dir:?}" ]; then
    rm -rv "${_project_dir:?}/${_install_dir:?}"
  fi
fi

# ---
#  build project in docker
# ---

(
  exec 1> >(>&1 awk '{print "[docker-stdout]: " $0}') # prefix stdout
  exec 2> >(>&2 awk '{print "[docker-stderr]: " $0}') # prefix stderr

  docker run \
    --rm \
    --user "${_uid}:${_guid}" \
    -v "${_project_dir}:/ty/src" \
    "${_arg_docker_image}" \
    bash -c "
      set -vx \
      && cd /ty/src \
      && cmake -S . -B '${_build_dir}' -G 'Unix Makefiles' \
          -DCMAKE_BUILD_TYPE=Release \
          -DCMAKE_INSTALL_PREFIX='${_install_dir}' \
          -DVCPKG_INSTALL_OPTIONS='--no-print-usage' \
          -DCMAKE_TOOLCHAIN_FILE=\${VCPKG_ROOT}/scripts/buildsystems/vcpkg.cmake \
          -DVCPKG_INSTALLED_DIR='/opt/vcpkg_installed' \
          -DVCPKG_TARGET_TRIPLET='x64-linux' \
      && cmake --build '${_build_dir}' --parallel \
      && cmake --install '${_build_dir}' \
      "
) || {
  __print_errormsg "docker run exited with non-zero error code"
  exit 1
}
