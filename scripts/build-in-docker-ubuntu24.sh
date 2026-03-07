#!/usr/bin/env bash

set -eo pipefail

_script_dir=$(readlink -f "$(dirname "$0")")

"${_script_dir}/build-in-docker.sh" "$@" "ty/ubuntu-buildtools:24.04" ubuntu24
