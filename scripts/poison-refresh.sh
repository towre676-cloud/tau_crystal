#!/usr/bin/env bash
set -Eeuo pipefail
IFS=$'\n\t'

retry() { n=0; until "$@"; do n=$((n+1)); [ "$n" -ge 5 ] && return 1; sleep 2; done; }

if command -v apt-get >/dev/null 2>&1; then
  sudo true || true
  retry sudo apt-get update
  retry sudo apt-get install -y jq curl git || true
fi

echo "[poison-refresh] completed"
exit 0
