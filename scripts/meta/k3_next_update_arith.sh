#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
python scripts/safe/arith_update.py receipts/k3_next_receipt.json data/k3_next_points.csv data/k3_next_heights.csv
./scripts/meta/k3_next_verify.sh || true
