#!/usr/bin/env bash
set -Eeuo pipefail

echo "[bootstrap] cwd: $(pwd)"

need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1"; exit 1; }; }

# Required CLIs
need python3
need jq
need bash

# Print versions
python3 -V
jq --version

# Optional: normalize line endings if tool is present (Windows-friendly)
if command -v dos2unix >/dev/null 2>&1; then
  dos2unix -q scripts/ci/*.py 2>/dev/null || true
fi

echo "[ok] deps present"
