#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
DIR="receipts/genus"
[ -d "$DIR" ] || mkdir -p "$DIR"
OUTCSV="$DIR/scan_report.csv"
> "$OUTCSV"
printf "%s\n" "target,generic,twisted,jump" >> "$OUTCSV"
for C in "$DIR"/*_coeffs.json; do [ -s "$C" ] || continue; T=$(basename "$C" "_coeffs.json"); O="$DIR/${T}_observation.json"; python scripts/safe/genus_reduce.py "$C" "$O"; g=$(python scripts/safe/json_read.py generic.zero_modes "$O"); z=$(python scripts/safe/json_read.py twisted.zero_modes "$O"); j=$(( ${z:-0} - ${g:-0} )); printf "%s\n" "${T},${g},${z},${j}" >> "$OUTCSV"; done
sort -t, -k4,4nr -k2,2n "$OUTCSV" -o "$OUTCSV"
tail -n +2 "$OUTCSV" | head -1 > "$DIR/top_candidate.txt" || true
printf "%s\n" "scan complete -> $OUTCSV"; [ -s "$DIR/top_candidate.txt" ] && { printf "%s\n" "top: $(cat "$DIR/top_candidate.txt")"; } || true
