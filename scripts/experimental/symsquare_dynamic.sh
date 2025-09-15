#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
PYBIN=python; command -v python >/dev/null 2>&1 || PYBIN="py -3"
in_json="${1:-}"; [ -n "$in_json" ] || { echo "supply hecke json"; exit 1; }
raw_out="$($PYBIN scripts/experimental/symsquare_dynamic.py "$in_json")"
$PYBIN scripts/experimental/_stamp_provenance.py "$raw_out"
echo "$raw_out"
