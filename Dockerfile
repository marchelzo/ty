FROM debian:latest

COPY . /usr/src/ty

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt install -y \
    g++ \
    gcc \
    git \
    libcurl4-openssl-dev \
    libffi-dev \
    libpcre3-dev \
    libreadline-dev \
    libsqlite3-dev \
    libssl-dev \
    libtool \
    libgumbo-dev \
    libsodium-dev \
    libutf8proc-dev \
    make \
    pkg-config \
    sqlite3 \
    sudo \
    wget \
 && apt clean \
 && rm -rf /var/lib/apt/lists/*
RUN ["sh", "-c", "cd /usr/src/ty/ && make clean && make && make install"]
