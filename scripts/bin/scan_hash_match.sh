#!/usr/bin/env bash
set -euo pipefail; set +H
TARGET="${1:?sha256 to find}"
shopt -s nullglob globstar 2>/dev/null || true
dirs=(contracts fixtures/contracts api schema doc .)
for d in "${dirs[@]}"; do
  [ -d "$d" ] || continue
  # skip bulky outputs
  find "$d" -type f -name "*.json" ! -path "analysis/*" ! -path "out/*" -print0 2>/dev/null | while IFS= read -r -d "" f; do
    h="$(scripts/bin/json_sha256.sh "$f" 2>/dev/null || true)"
    [ "$h" = "$TARGET" ] && { printf "%s\n" "$f"; exit 0; }
  done
done
exit 1
