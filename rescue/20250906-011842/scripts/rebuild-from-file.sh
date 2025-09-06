#!/usr/bin/env bash
set -u
INFILE="${1:-tmp/P2P.ndjson}"
: "${TAU_MIN:=0.06}"
: "${TAU_SLOPE:=0.30}"
export TAU_MIN TAU_SLOPE
rm -f manifests/*.json 2>/dev/null || true
PYBIN="$(command -v python3 || command -v python || true)"
[ -z "$PYBIN" ] && { echo "[rebuild] python not found"; exit 0; }
"$PYBIN" sidecar/process_file.py "$INFILE" || true
scripts/verify-all.sh
