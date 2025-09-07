#!/usr/bin/env bash
set -euo pipefail
dry=0
if [ "${1:-}" = "--dry" ]; then dry=1; shift; fi
f="${1:-lakefile.lean}"
[ -f "$f" ] || { echo "[err] not found: $f"; exit 1; }

bak="$f.bak.$(date +%Y%m%dT%H%M%SZ)"
cp -f "$f" "$bak"
tmp="$(mktemp)"

# normalize line endings, drop code-fences, strip lone backticks
awk '{sub(/\r$/,""); print}' "$bak" \
| awk '!/^\s*```/' \
| sed 's/`//g' \
> "$tmp"

if cmp -s "$f" "$tmp"; then
  echo "[fix] no changes needed"
  rm -f "$tmp"
  exit 0
fi

if [ $dry -eq 1 ]; then
  echo "[diff] (dry-run) showing changes:"
  git --no-pager diff --no-index -- "$f" "$tmp" || true
  rm -f "$tmp"
  echo "[fix] dry-run complete; kept backup: $bak"
  exit 0
fi

mv "$tmp" "$f"
echo "[fix] wrote sanitized file; backup: $bak"
git --no-pager diff --no-index -- "$bak" "$f" || true
