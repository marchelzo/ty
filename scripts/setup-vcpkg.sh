#!/usr/bin/bash

set -e

_script_dir=$(readlink -f "$(dirname "${BASH_SOURCE[0]}")")
_project_dir=$(readlink -f "${_script_dir}/..")
_vcpkg_root="${_project_dir}/_vcpkg"

if [[ -d "${_vcpkg_root}/.git" ]]; then
  git -C "${_vcpkg_root}" pull
else
  git clone "https://github.com/microsoft/vcpkg.git" "${_vcpkg_root}"
  "${_vcpkg_root}/bootstrap-vcpkg.sh"
fi

function __path_remove() { # arg1 <DIR>
  PATH=${PATH//":${1}:"/:} # delete all instances in the middle
  PATH=${PATH/%":${1}"/}   # delete any instance at the end
  PATH=${PATH/#"${1}:"/}   # delete any instance at the beginning
}

function __path_prepend() { # arg1 DIR>
  __path_remove "${1}"
  PATH="${1}${PATH:+":$PATH"}"
}

__path_prepend "${_vcpkg_root}"
export VCPKG_ROOT="${_vcpkg_root}"
