#!/usr/bin/env bash
set -Eeuo pipefail

# Load tunables if present
if [ -f .github/ci.env ]; then
  # shellcheck source=/dev/null
  . .github/ci.env
fi
: "${TESTS_PER_SHARD:=60}"
: "${MATRIX_MAX_SHARDS:=16}"

# Count test files deterministically
mapfile -t files < <(git ls-files \
  | grep -E '(^|/)(tests?/(.+)\.(py|rs|go|js|ts|jsx|tsx)$|(.+)\.test\.(js|ts|jsx|tsx)$|(.+)_test\.(py|rs|go)$)' \
  | sort)
n=${#files[@]}

# Derive shard count from footprint, clamp [1, MATRIX_MAX_SHARDS]
if (( n == 0 )); then
  shards=1
else
  # ceil(n / TESTS_PER_SHARD)
  shards=$(( (n + TESTS_PER_SHARD - 1) / TESTS_PER_SHARD ))
fi
(( shards < 1 )) && shards=1
(( shards > MATRIX_MAX_SHARDS )) && shards=$MATRIX_MAX_SHARDS

# Emit JSON matrix like: {"shard":[0,1,2,...]}
json='{"shard":['
for ((i=0;i<shards;i++)); do
  json+="$i"
  (( i < shards-1 )) && json+=","
done
json+=']}'

echo "matrix=$json"       >> "$GITHUB_OUTPUT"
echo "total=$shards"      >> "$GITHUB_OUTPUT"
echo "tests=$n"           >> "$GITHUB_OUTPUT"
echo "[info] tests=$n shards=$shards" 1>&2
