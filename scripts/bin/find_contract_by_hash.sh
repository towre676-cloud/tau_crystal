#!/usr/bin/env bash
set -euo pipefail; set +H
REC="${1:?path to receipt.json}"
if command -v jq >/dev/null 2>&1; then
  H_IN="$(jq -r ".input_sha256" "$REC")"
else
  H_IN="$(grep -o "\"input_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | head -n1 | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"
fi
[ -n "$H_IN" ] || { echo "[err] no input_sha256 in $REC" >&2; exit 2; }
found=""
if command -v find >/dev/null 2>&1; then
  while IFS= read -r -d "" c; do
    h="$(scripts/bin/json_sha256.sh "$c")"
    if [ "$h" = "$H_IN" ]; then found="$c"; echo "$c"; exit 0; fi
  done < <(find contracts -type f -name "*.json" -print0 2>/dev/null)
else
  shopt -s nullglob globstar 2>/dev/null || true
  for c in contracts/**/*.json contracts/*.json; do
    h="$(scripts/bin/json_sha256.sh "$c")"
    if [ "$h" = "$H_IN" ]; then found="$c"; echo "$c"; exit 0; fi
  done
fi
echo "[err] no matching contract file for input_sha256 in $REC" >&2; exit 3
