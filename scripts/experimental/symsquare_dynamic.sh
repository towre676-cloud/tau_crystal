#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
in_json="${1:-}"
[ -n "$in_json" ] || { echo "supply hecke json"; exit 1; }
raw_out=$(python scripts/experimental/symsquare_dynamic.py "$in_json")
python scripts/experimental/_stamp_provenance.py "$raw_out"
echo "$raw_out"
