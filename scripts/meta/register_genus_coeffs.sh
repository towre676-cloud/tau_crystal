#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
T="$1"; SRC="$2"
[ -n "$T" ] && [ -n "$SRC" ] || { echo "usage: register_genus_coeffs.sh <TARGET_ID> <coeffs.json>" >&2; exit 2; }
[ -s "$SRC" ] || { echo "missing coeffs at $SRC" >&2; exit 3; }
DST="receipts/genus/${T}_coeffs.json"
cp -f "$SRC" "$DST"
python scripts/safe/genus_reduce.py "$DST" "receipts/genus/${T}_observation.json"
./scripts/meta/scan_candidates.sh >/dev/null 2>&1 || true
echo "$DST"
