#!/bin/sh

set -eu

orig=$1
out=${2:-}

fail() {
        echo "$0: $*" >&2
        exit 1
}

hex() {
        printf %016x $(($1))
}

section() {
        readelf -SW "$1" | sed 's/^ *\[ *[0-9]*\] *//' | awk -v s="$2" '$1 == s { print "0x" $3, "0x" $5 }'
}

offset() {
        readelf -lW "$1" | while read -r type off va pa fsz rest; do
                if [ "$type" = LOAD ] && [ $(($2)) -ge $((va)) ] && [ $(($2)) -lt $((va + fsz)) ]; then
                        echo $(($2 - va + off))
                fi
        done
}

quad() {
        r=$(echo "$rel" | awk -v a="$(hex "$1")" '$1 == a { print "0x" $2 }')
        echo "${r:-$(od -An -t u8 -j "$(offset "$orig" "$1")" -N 8 "$orig")}"
}

owner() {
        nm -nS --defined-only "$orig" | awk -v a="$(hex "$1")" '($1 "") <= a && ($3 == "t" || $3 == "T") { s = $1 " " $2 " " $4 } END { print s }'
}

same() {
        cmp -s -n $(($2)) "$orig" "$out" "$(offset "$orig" "$1")" "$(offset "$out" "$1")"
}

set -- $(section "$orig" __rseq_cs)

if [ $# -eq 0 ]; then
        exit 0
fi

base=$1
size=$2
rel=$(readelf -rW "$orig" | awk -v lo="$(hex "$base")" -v hi="$(hex $((base + size)))" '$3 ~ /_RELATIVE$/ && ($1 "") >= lo && ($1 "") < hi { print $1, $4 }')
names=

for cs in $(seq $((base)) 32 $((base + size - 32))); do
        start=$(quad $((cs + 8)))
        len=$(quad $((cs + 16)))
        abort=$(quad $((cs + 24)))
        set -- $(owner "$start") "" "" ""
        if [ -z "$3" ] || [ $((0x$1 + 0x$2)) -le $((start)) ]; then
                fail "no function contains the rseq critical section at $(printf %#x $((start)))"
        fi
        if
                [ -n "$out" ] && {
                        ! nm "$out" | grep -q "^$1 [tT] $3\$" \
                     || ! same "$start" "$len" \
                     || ! same $((abort - 4)) 4
                }
        then
                fail "rseq critical section at $(printf %#x $((start))) in $3 moved or changed in $out"
        fi
        names="$names$3
"
done

if [ -z "$out" ]; then
        printf %s "$names" | sort -u | paste -sd '|' -
fi
