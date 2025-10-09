#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
J=receipts/e29_receipt.json
[ -s "$J" ] || { echo "missing $J" >&2; exit 2; }
py() { python "scripts/safe/json_read.py" "$1" "$J"; }
rank=$(py curve.proven_rank)
wnum=$(py curve.root_number)
gr=$(py fibration.generic_mordell_weil_rank)
sr=$(py fibration.special_fiber_rank)
rj=$(py fibration.rank_increase)
[ "$rank" = "29" ] && [ "$wnum" = "-1" ] && [ "$gr" = "17" ] && [ "$sr" = "29" ] && [ "$rj" = "12" ] && { echo PASS; exit 0; } || { echo FAIL "rank=$rank w=$wnum gr=$gr sr=$sr rj=$rj"; exit 1; }
