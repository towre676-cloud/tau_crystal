#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
REC="receipts/k3_next_receipt.json"; MX="data/k3_next_height_full.csv"; OUT="receipts/k3_next_regulator_full.json"
[ -s "$MX" ] || { echo "missing $MX" >&2; exit 2; }
python scripts/safe/height_full_det.py "$REC" "$MX" "$OUT"
./scripts/meta/k3_next_verify.sh || true
