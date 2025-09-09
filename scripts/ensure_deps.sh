#!/usr/bin/env bash
set -euo pipefail
# Only runs on Ubuntu CI runners; harmless locally on Windows.
if command -v apt-get >/dev/null 2>&1; then
  sudo apt-get update -y
  sudo DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends jq curl ca-certificates git python3 python3-pip openssl coreutils awscli b3sum
fi
# OpenTimestamps client (anchors to Bitcoin); ignore if pip unavailable locally
python3 -m pip install --user --no-warn-script-location opentimestamps-client >/dev/null 2>&1 || true
echo "[ok] deps ready: jq curl awscli b3sum OpenTimestamps"
