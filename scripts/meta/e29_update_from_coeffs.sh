#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"
cd "$CD" || exit 1
IN=receipts/e29_genus_coeffs.json
OUT=receipts/e29_genus_observation.json
[ -s "$IN" ] || { echo "missing $IN" >&2; exit 2; }
python scripts/safe/genus_reduce.py "$IN" "$OUT"
./scripts/meta/e29_compare.sh || true
