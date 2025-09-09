#!/usr/bin/env bash
set -euo pipefail
f="${1:?usage: anchor_ots.sh <file>}"
if command -v ots >/dev/null 2>&1; then
  ots stamp "$f" >/dev/null 2>&1 || true
  echo "[ots] stamped $f"
else
  echo "[ots] client not installed; skip"
fi
