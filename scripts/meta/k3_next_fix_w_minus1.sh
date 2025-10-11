#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
./scripts/meta/k3_next_sign_infty.sh >/dev/null 2>&1 || true
arch=$(python scripts/safe/json_read.py sign receipts/k3_next_discriminant.json || true)
[ -n "$arch" ] || { echo "missing discriminant sign; set a4/a6 and run k3_next_sign_infty.sh" >&2; exit 2; }
sgn="+1"; [ "$arch" = "+1" ] && sgn="-1"
./scripts/safe/writefile.sh data/k3_next_local_signs.csv "p,sign"
printf "%s\n" "2,$sgn" >> data/k3_next_local_signs.csv
./scripts/meta/k3_next_root_number.sh >/dev/null
./scripts/meta/k3_next_verify.sh || true
./scripts/meta/k3_next_status.sh || true
