#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
file="${1:-}"; [ -f "$file" ] || { echo "[err] file not found: $file"; exit 2; }
if command -v pv >/dev/null 2>&1; then
  pv "$file" >/dev/null
else
  cat "$file" >/dev/null
fi
echo "[OK] processed $file"
