#!/usr/bin/env bash
set -Eeuo pipefail; set +H
manifest="${1:-}"
[ -n "$manifest" ] || { echo "[err] missing manifest path" >&2; echo "error"; exit 0; }
if [ ! -f "$manifest" ]; then
  echo "::error file=$manifest::manifest not found"
  echo "error"; exit 0
fi
status="ok"
if [ -x scripts/spec_guard.sh ] && ! bash scripts/spec_guard.sh; then status="mismatch"; fi
echo "$status"
exit 0
