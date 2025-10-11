#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
MIN="${1:-12}"
./scripts/meta/scan_candidates.sh >/dev/null
IN="receipts/genus/scan_report.csv"; OUT="receipts/genus/scan_over_${MIN}.csv"
[ -s "$IN" ] || { echo "no scan_report.csv"; exit 2; }
> "$OUT"
printf "%s\n" "target,generic,twisted,jump" >> "$OUT"
tail -n +2 "$IN" | awk -F, -v m="$MIN" '{ if ($4+0 >= m) print $0 }' >> "$OUT"
echo "filtered -> $OUT"; [ $(wc -l < "$OUT") -gt 1 ] && tail -n +2 "$OUT" | head -1 > receipts/genus/top_candidate.txt || true
