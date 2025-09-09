#!/usr/bin/env bash
set -euo pipefail
if command -v apt-get >/dev/null 2>&1; then
  sudo apt-get update -y
  sudo DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    jq curl ca-certificates git python3 python3-pip b3sum
  python3 -m pip install --user --no-warn-script-location opentimestamps-client >/dev/null 2>&1 || true
fi
echo "[ok] deps ready"
