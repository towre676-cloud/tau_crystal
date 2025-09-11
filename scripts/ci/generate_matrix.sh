#!/usr/bin/env bash
set -Eeuo pipefail
# Count test files deterministically
mapfile -t files < <(git ls-files \
  | grep -E '(^|/)(tests?/(.+)\.(py|rs|go|js|ts|jsx|tsx)$|(.+)\.test\.(js|ts|jsx|tsx)$|(.+)_test\.(py|rs|go)$)' \
  | sort)
n=${#files[@]}
# Derive shard count: ~60 tests per shard, clamp [1,16]
if (( n == 0 )); then shards=1; else shards=$(( (n + 59) / 60 )); fi
(( shards < 1 )) && shards=1
(( shards > 16 )) && shards=16
# Emit JSON matrix like: {"shard":[0,1,2]}
json='{"shard":['
for ((i=0;i<shards;i++)); do
  json+="$i"
  (( i < shards-1 )) && json+=","
done
json+=']}'
echo "matrix=$json"       >> "$GITHUB_OUTPUT"
echo "total=$shards"      >> "$GITHUB_OUTPUT"
echo "tests=$n"         >> "$GITHUB_OUTPUT"
echo "[info] tests=$n shards=$shards" 1>&2

