#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"
cd "$CD" || exit 1
IN="$1"; OUT="$2"
[ -n "$IN" ] && [ -n "$OUT" ] || { echo "usage: genus_from_coeffs.sh <coeffs.json> <observation.json>" >&2; exit 2; }
[ -s "$IN" ] || { echo "missing $IN" >&2; exit 3; }
python scripts/safe/genus_reduce.py "$IN" "$OUT"
printf "%s\n" "$OUT"
