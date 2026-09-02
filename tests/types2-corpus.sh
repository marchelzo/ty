#!/bin/sh

set -eu

ty_bin=${1:-./ty}
case "$ty_bin" in
/*) ;;
*) ty_bin=$(pwd)/$ty_bin ;;
esac

test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root_dir=$(CDPATH= cd -- "$test_dir/.." && pwd)
classification=$test_dir/types2-corpus-classification.json
scratch=$(mktemp -d "${TMPDIR:-/tmp}/ty-types2-corpus.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT HUP INT TERM

asan_options=${ASAN_OPTIONS:-}
if [ -n "$asan_options" ]; then
        asan_options=$asan_options:intercept_strndup=0
else
        asan_options=intercept_strndup=0
fi

ASAN_OPTIONS=$asan_options \
        TY_TYPES2_LOG="$scratch/corpus.jsonl" \
        TY_TYPES2_TRACE_DEFERRED=1 \
        "$ty_bin" -c -e nil

ASAN_OPTIONS=$asan_options \
        "$ty_bin" "$root_dir/tools/types2-corpus-summary.ty" \
        --strict \
        --classification "$classification" \
        "$scratch/corpus.jsonl"
