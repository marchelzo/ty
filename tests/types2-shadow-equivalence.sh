#!/bin/sh

set -eu

ty_bin=${1:-./ty}
case "$ty_bin" in
/*) ;;
*) ty_bin=$(pwd)/$ty_bin ;;
esac

test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/ty-types2-shadow.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT HUP INT TERM

asan_options=${ASAN_OPTIONS:-}
if [ -n "$asan_options" ]; then
        asan_options=$asan_options:intercept_strndup=0
else
        asan_options=intercept_strndup=0
fi

run_case()
{
        mode=$1
        source=$2
        stdout=$3
        stderr=$4
        status=$5

        set +e
        if [ "$mode" = disabled ]; then
                ASAN_OPTIONS=$asan_options TY_TYPES2_SHADOW=0 \
                        "$ty_bin" "$source" >"$stdout" 2>"$stderr"
        elif [ "$mode" = traced ]; then
                ASAN_OPTIONS=$asan_options \
                        TY_TYPES2_LOG="$scratch/trace.jsonl" \
                        TY_TYPES2_TRACE_NODES=1 \
                        "$ty_bin" "$source" >"$stdout" 2>"$stderr"
        else
                ASAN_OPTIONS=$asan_options TY_TYPES2_LOG="$scratch/shadow.jsonl" \
                        "$ty_bin" "$source" >"$stdout" 2>"$stderr"
        fi
        result=$?
        set -e

        printf '%s\n' "$result" >"$status"
}

for fixture in valid invalid overload-union flow flow-invalidation contracts class-operator operator-constraints pack-constraints scoped-obligations subscript-protocol member-protocol keyword-spread match-coverage recovery; do
        source=$test_dir/fixtures/types2-shadow-$fixture.ty.txt

        run_case \
                disabled \
                "$source" \
                "$scratch/$fixture.disabled.out" \
                "$scratch/$fixture.disabled.err" \
                "$scratch/$fixture.disabled.status"

        run_case \
                enabled \
                "$source" \
                "$scratch/$fixture.enabled.out" \
                "$scratch/$fixture.enabled.err" \
                "$scratch/$fixture.enabled.status"

        cmp "$scratch/$fixture.disabled.out" "$scratch/$fixture.enabled.out"
        cmp "$scratch/$fixture.disabled.err" "$scratch/$fixture.enabled.err"
        cmp "$scratch/$fixture.disabled.status" "$scratch/$fixture.enabled.status"
done

run_case \
        traced \
        "$test_dir/fixtures/types2-shadow-recovery.ty.txt" \
        "$scratch/recovery.traced.out" \
        "$scratch/recovery.traced.err" \
        "$scratch/recovery.traced.status"
cmp "$scratch/recovery.disabled.out" "$scratch/recovery.traced.out"
cmp "$scratch/recovery.disabled.err" "$scratch/recovery.traced.err"
cmp "$scratch/recovery.disabled.status" "$scratch/recovery.traced.status"
grep -q '"event":"node_type"' "$scratch/trace.jsonl"
grep -Eq '"event":"node_type".*"runtime_kind":"(int|string|function|nominal)".*"runtime_exact":true' \
        "$scratch/trace.jsonl"
grep -Eq '"event":"node_type".*"construct":"TYPE_OF".*"runtime_kind":"type_value".*"runtime_exact":true' \
        "$scratch/trace.jsonl"

grep -q '"event":"begin"' "$scratch/shadow.jsonl"
grep -q '"event":"checkpoint"' "$scratch/shadow.jsonl"
grep -q '"event":"finish"' "$scratch/shadow.jsonl"
grep -q '"event":"abort"' "$scratch/shadow.jsonl"
grep -Eq '"union_call_splits":[1-9][0-9]*' "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-flow.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-flow-invalidation.ty.txt".*"code":"union-(member|method)-coverage"' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-contracts.ty.txt".*"code":"missing-trait-member"' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-contracts.ty.txt".*"code":"invalid-trait-member"' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-contracts.ty.txt".*"code":"invalid-override"' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-class-operator.ty.txt".*"class_operator_declarations":[1-9][0-9]*' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-class-operator.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-operator-constraints.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-operator-constraints.ty.txt".*"pending_obligations":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-pack-constraints.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-pack-constraints.ty.txt".*"pending_obligations":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-scoped-obligations.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-scoped-obligations.ty.txt".*"pending_obligations":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-subscript-protocol.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-subscript-protocol.ty.txt".*"pending_obligations":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-member-protocol.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-member-protocol.ty.txt".*"pending_obligations":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-keyword-spread.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-keyword-spread.ty.txt".*"pending_obligations":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-match-coverage.ty.txt".*"code":"unreachable-pattern"' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-match-coverage.ty.txt".*"code":"non-exhaustive-match"' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-match-coverage.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-match-coverage.ty.txt".*"types2_warnings":2' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-match-coverage.ty.txt".*"pending_obligations":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-recovery.ty.txt".*"types2_errors":0' \
        "$scratch/shadow.jsonl"
grep -Eq '"path":"[^"]*types2-shadow-recovery.ty.txt".*"pending_obligations":0' \
        "$scratch/shadow.jsonl"

printf 'types2 shadow equivalence: ok\n'
