#!/usr/bin/env bash
set -Eeuo pipefail; set +H
manifest="${1:-}"
[ -n "$manifest" ] || { echo "[err] missing manifest path" >&2; echo "error"; exit 0; }
if [ ! -f "$manifest" ]; then
  echo "::error file=$manifest::manifest not found"
  echo "error"; exit 0
fi

status="ok"
# Prefer your existing spec_guard if present
if [ -x scripts/spec_guard.sh ]; then
  if ! bash scripts/spec_guard.sh; then
    status="mismatch"
  fi
fi

echo "$status"
exit 0
