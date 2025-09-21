#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here"
if ! command -v lake >/dev/null 2>&1; then echo "Lake not found. Install Lean 4 toolchain."; exit 1; fi
# lake update (disabled)
lake build
lake env lean --run Src/Spectral/plumbing.lean > trace.json
echo "[ok] wrote trace.json"
if command -v python3 >/dev/null 2>&1; then python3 draw.py trace.json; else echo "python3 not found; trace is in trace.json"; fi
