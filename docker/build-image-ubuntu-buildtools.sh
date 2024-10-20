#!/usr/bin/env sh

_script_dir=$(readlink -f "$(dirname "$0")")
_project_dir=$(readlink -f "${_script_dir}/..")

# ---
#  input variables
# ---

_default_cmake_version="3.21.7"
_default_ubuntu_version="latest"
_default_image_prefix="ty"
_default_image_tag="\${UBUNTU_VERSION}"
_default_registry_url=""
_default_vcpkg_file="${_project_dir}/vcpkg.json"

# -- always fallback to the default
CMAKE_VERSION=${CMAKE_VERSION:-${_default_cmake_version}}
UBUNTU_VERSION=${UBUNTU_VERSION:-${_default_ubuntu_version}}
VCPKG_FILE=${VCPKG_FILE:-${_default_vcpkg_file}}
# -- allowed to be specified as empty by the user
IMAGE_PREFIX=${IMAGE_PREFIX-${_default_image_prefix}}
IMAGE_TAG=${IMAGE_TAG-$(eval echo "${_default_image_tag}")}
REGISTRY_URL=${REGISTRY_URL-${_default_registry_url}}

# ensure that non-empty image prefixes always end in trailing slash
if [ -n "${IMAGE_PREFIX}" ] && [ "${IMAGE_PREFIX#"${IMAGE_PREFIX%?}"}" != "/" ];
then
  IMAGE_PREFIX=${IMAGE_PREFIX}/
fi
# ensure that non-empty registry url ends in trailing slash
if [ -n "${REGISTRY_URL}" ] && [ "${REGISTRY_URL#"${REGISTRY_URL%?}"}" != "/" ];
then
  REGISTRY_URL=${REGISTRY_URL}/
fi
# ensure that non-empty image tag doesn't start with a colon
if [ -n "${IMAGE_TAG}" ]; then
  IMAGE_TAG=${IMAGE_TAG#:}
fi

# ---
#  functions
# ---

__print_usage() {
  >&2 cat <<EOF

  USAGE: $(basename "$0") [OPTIONS] -- [DOCKER_OPTIONS]

    Builds a docker image containing the build tools needed to compile ty

      - '\${IMAGE_PREFIX}/ubuntu-buildtools:\${IMAGE_TAG}'

    OPTIONS
      -h --help   show this usage text

    The following variables can be set in current shell environment to override
    the default values used by this script:

      UBUNTU_VERSION   [default=${_default_ubuntu_version}]
      VCPKG_FILE       [default=${_default_vcpkg_file}]
      IMAGE_PREFIX     [default=${_default_image_prefix}]
      IMAGE_TAG        [default=${_default_image_tag}]
      REGISTRY_URL     [default=${_default_registry_url}]

EOF
}

# ---
#  parse arguments
# ---

while [ -n "$1" ]
do
  case "$1" in
    -h|--help) __print_usage; exit 0 ;;
    --)        shift; break ;;
    *)         2>&1 echo "invalid input '$1'"; exit 1 ;;
  esac
  shift
done

# ---
#  copy vcpkg.json into temp directory used for isolated docker context
# ---

if [ ! -f "${VCPKG_FILE}" ]; then
  2>&1 echo "provided \$VCPKG_FILE does not exist: ${VCPKG_FILE}"
  exit 1
fi

_build_context_dir="${_project_dir}/docker/_build_context"
mkdir -p "$_build_context_dir"
cp "$VCPKG_FILE" "$_build_context_dir"

# ---
#  build image
# ---

cd "${_script_dir}" || exit 1

set -vx
DOCKER_BUILDKIT=1 docker build \
  --tag "${IMAGE_PREFIX}ubuntu-buildtools:${IMAGE_TAG}" \
  --build-arg REGISTRY_URL="${REGISTRY_URL}" \
  --build-arg CMAKE_VERSION="${CMAKE_VERSION}" \
  --build-arg UBUNTU_VERSION="${UBUNTU_VERSION}" \
  --rm \
  --file "${_script_dir}/ubuntu-buildtools.dockerfile" \
  "$@" \
  "${_build_context_dir}"
set +vx
