#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
J=receipts/e29_receipt.json
p(){ python scripts/safe/json_read.py "$1" "$J"; }
echo "E29: y^2 + x*y = x^3 + a4*x + a6"
echo "a4: $(p curve.a4)"
echo "a6: $(p curve.a6)"
echo "root number: $(p curve.root_number)"
echo "proven rank: $(p curve.proven_rank)"
echo "generic MW rank: $(p fibration.generic_mordell_weil_rank) → special: $(p fibration.special_fiber_rank)"
echo "— Independent points (x,y) —"
nl=$'\n'; n=0; while IFS=, read -r X Y; do
  case "$X" in x) continue ;; \#*|"") continue ;; esac
  n=$((n+1)); printf "P%-2d = [%s, %s]%s" "$n" "$X" "$Y" "$nl"
done < data/e29_points.csv
