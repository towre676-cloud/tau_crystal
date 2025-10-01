#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -e
OLD=".tau_ledger/hysteresis/barcode_ref.json"
NEW=".tau_ledger/hysteresis/latest_barcode.json"
LIMIT_FILE=".tau_ledger/stability/thresholds.json"
BOTTLE=$(jq -r '.barcode_bottleneck' "$LIMIT_FILE" 2>/dev/null || echo 0.005)

[ -s "$OLD" ] || printf '%s\n' '{"loop_area":0.000}' > "$OLD"
[ -s "$NEW" ] || printf '%s\n' '{"loop_area":0.000}' > "$NEW"

DELTA=$(jq -s '(.[0].loop_area//0) as $a | (.[1].loop_area//0) as $b
  | ($b - $a) | if .<0 then -. else . end' "$OLD" "$NEW")

awk -v delta="$DELTA" -v bottle="$BOTTLE" 'BEGIN{
  if (delta+0.0 > bottle+0.0){ printf "[FAIL] Barcode regression exceeds bottleneck threshold: %.6f\n", delta; exit 66 }
  else { printf "[PASS] Barcode delta acceptable: %.6f\n", delta; exit 0 }
}'
