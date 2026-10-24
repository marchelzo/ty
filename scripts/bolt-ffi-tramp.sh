#!/bin/sh

set -eu

orig=$1
out=$2
sym=trampoline_code_table

symbol() {
        nm -S "$1" | awk -v s="$sym" '$4 == s { print "0x" $1, "0x" $2 }'
}

offset() {
        readelf -lW "$1" | while read -r type off va pa fsz rest; do
                if [ "$type" = LOAD ] && [ $(($2)) -ge $((va)) ] && [ $(($2)) -lt $((va + fsz)) ]; then
                        echo $(($2 - va + off))
                fi
        done
}

set -- $(symbol "$orig")

if [ $# -eq 0 ]; then
        exit 0
fi

addr=$1
size=$2

set -- $(symbol "$out")

if [ "${1:-}" != "$addr" ]; then
        echo "$0: $sym moved from $addr to ${1:-nowhere} in $out (missing from BOLT_SKIP?)" >&2
        exit 1
fi

dd if="$orig" of="$out" bs=1 count=$((size)) conv=notrunc status=none \
   skip="$(offset "$orig" "$addr")" seek="$(offset "$out" "$addr")"
