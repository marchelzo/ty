ARG REGISTRY_URL=""
ARG CMAKE_VERSION="3.21.7"
ARG UBUNTU_VERSION="latest"
ARG USER_ID=1000
ARG GROUP_ID=1000

# ---
#  stage: establish external dependencies
# ---

FROM ${REGISTRY_URL}ubuntu:${UBUNTU_VERSION} AS base-os

# ---
#  stage: setup layer that can be used to dl from internet
# ---

SHELL ["bash", "-c"]

FROM base-os AS apt-install

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
    "tar" \
    "xz-utils" \
    "curl" \
    "ca-certificates" \
    "git" \
    "pkg-config" \
    "zip" \
    "luajit" \
    "gperf" \
    "unzip" \
    "build-essential" \
    && apt-get clean -y \
    && rm -fr /var/lib/apt/lists

# -- switch container default user to 'user'

RUN chmod -R 777 /opt
ARG USER_ID
ARG GROUP_ID
RUN if getent group ${GROUP_ID} >/dev/null 2>&1; then \
      groupmod -n "user" $(getent group ${GROUP_ID} | cut -d: -f1); \
    else \
      groupadd -g ${GROUP_ID} "user"; \
    fi \
    && if id -u ${USER_ID} >/dev/null 2>&1; then \
         usermod -l "user" -g "user" -d /home/user -m $(getent passwd ${USER_ID} | cut -d: -f1); \
       else \
         useradd -u ${USER_ID} -g "user" -m "user"; \
       fi
USER "user"

# -- download vcpkg

ENV VCPKG_ROOT=/opt/vcpkg

RUN git clone https://github.com/microsoft/vcpkg.git "${VCPKG_ROOT}" \
    && "${VCPKG_ROOT}/bootstrap-vcpkg.sh"

# -- copy manifest and install project dependencies

WORKDIR /opt
COPY vcpkg.json /opt/vcpkg.json
RUN "${VCPKG_ROOT}/vcpkg" install --triplet x64-linux

# -- download our own copy of cmake because vcpkg selfishly hoards its own

ARG CMAKE_VERSION
RUN set -eo pipefail \
    && base_url="https://github.com/Kitware/CMake/releases/download" \
    && url="${base_url}/v${CMAKE_VERSION}/cmake-${CMAKE_VERSION}-linux-x86_64.tar.gz" \
    && mkdir -p /opt/cmake \
    && (curl -sL "$url" | tar --strip-components=1 -xz -C /opt/cmake) \
    && rm -fr /opt/cmake/bin/ccmake /opt/cmake/bin/cmake-gui
ENV PATH=/opt/cmake/bin:${PATH}

# ENV VCPKG_INSTALL_OPTIONS="--no-print-usage"
# ENV CMAKE_TOOLCHAIN_FILE="${VCPKG_ROOT}/scripts/buildsystems/vcpkg.cmake"
# ENV VCPKG_INSTALLED_DIR="/opt/vcpkg_installed"
