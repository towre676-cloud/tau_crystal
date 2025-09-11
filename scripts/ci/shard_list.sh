#!/usr/bin/env bash
set -Eeuo pipefail
shard="${1:-0}"
total="${2:-1}"

# Gather candidate test files using git ls-files for determinism
# Patterns: pytest-style, Go *_test.go, Rust *_test.rs, JS/TS .test.
mapfile -t files < <(git ls-files \
  | grep -E '(^|/)(tests?/.*\.(py|rs|go|js|ts)$|.*(\.test\.(js|ts|jsx|tsx)|_test\.(py|rs|go))$)' \
  | sort)

mkdir -p .tau_ledger
tmp=".tau_ledger/shard-files.txt"
: > "$tmp"

if [ "${#files[@]}" -eq 0 ]; then
  echo "filesfile=$tmp" >> "$GITHUB_OUTPUT" || true
  echo "count=0"        >> "$GITHUB_OUTPUT" || true
  exit 0
fi

idx=0
for f in "${files[@]}"; do
  # stable modulo by index
  if (( idx % total == shard )); then
    printf '%s\n' "$f" >> "$tmp"
  fi
  ((idx++))
done

count=$(wc -l < "$tmp" | tr -d '[:space:]')
echo "filesfile=$tmp" >> "$GITHUB_OUTPUT"
echo "count=$count"   >> "$GITHUB_OUTPUT"
