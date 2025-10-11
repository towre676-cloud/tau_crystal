#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
MIN="${1:-12}"
./scripts/meta/scan_threshold.sh "$MIN" >/dev/null
R="receipts/genus/top_candidate.txt"; [ -s "$R" ] || { echo "no candidates over threshold"; exit 3; }
./scripts/meta/promote_top_candidate.sh
