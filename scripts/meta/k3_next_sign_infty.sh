#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
REC="receipts/k3_next_receipt.json"; OUT="receipts/k3_next_discriminant.json"
python scripts/safe/sign_at_infinity.py "$REC" "$OUT"
cat "$OUT"
