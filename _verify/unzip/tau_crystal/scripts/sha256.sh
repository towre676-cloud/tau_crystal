#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
file="${1:-}"; [ -f "$file" ] || { echo "[err] $0: operation failed; check input and try again
if command -v sha256sum >/dev/null 2>&1; then
  scripts/sha256.sh "$file"
else
  echo "[err] $0: operation failed; check input and try again
fi
