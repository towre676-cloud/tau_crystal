#!/usr/bin/env bash
set -Eeuo pipefail
shard="${1:-0}"
total="${2:-1}"

# Collect candidate tests deterministically
mapfile -t files < <(git ls-files \
  | grep -E '(^|/)(tests?/(.+)\.(py|rs|go|js|ts|jsx|tsx)$|(.+)\.test\.(js|ts|jsx|tsx)$|(.+)_test\.(py|rs|go)$)' \
  | sort)

mkdir -p .tau_ledger
out=".tau_ledger/shard-files.txt"
: > "$out"

if [ "${#files[@]}" -eq 0 ]; then
  echo "filesfile=$out" >> "$GITHUB_OUTPUT" 2>/dev/null || true
  echo "count=0"        >> "$GITHUB_OUTPUT" 2>/dev/null || true
  exit 0
fi

i=0
for f in "${files[@]}"; do
  if (( i % total == shard )); then printf '%s\n' "$f" >> "$out"; fi
  ((i++))
done

cnt=$(wc -l < "$out" | tr -d '[:space:]')
echo "filesfile=$out" >> "$GITHUB_OUTPUT" 2>/dev/null || true
echo "count=$cnt"     >> "$GITHUB_OUTPUT" 2>/dev/null || true
