#!/usr/bin/env bash
set -euo pipefail
algo="blake3"
if command -v b3sum >/dev/null 2>&1; then
  b3sum "$1" | awk '{print $1" blake3"}'
else
  # Dev-only shim to keep local runs working; CI installs real b3sum via apt or cargo
  sha256sum "$1" | awk '{print $1" sha256"}'
  algo="sha256"
fi
