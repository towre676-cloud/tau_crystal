#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
REC="receipts/k3_next_receipt.json"; MX="data/k3_next_height_matrix.csv"; OUT="receipts/k3_next_regulator.json"
[ -s "$REC" ] && [ -s "$MX" ] || { echo "missing $REC or $MX" >&2; exit 2; }
python scripts/safe/height_det.py "$REC" "$MX" "$OUT"
./scripts/meta/k3_next_verify.sh || true
