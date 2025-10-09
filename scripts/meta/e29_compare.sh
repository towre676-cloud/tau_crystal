#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
JR=receipts/e29_receipt.json
JG=receipts/e29_genus_observation.json
[ -s "$JR" ] && [ -s "$JG" ] || { echo "missing receipts" >&2; exit 2; }
pyr() { python scripts/safe/json_read.py "$1" "$JR"; }
pyg() { python scripts/safe/json_read.py "$1" "$JG"; }
rank=$(pyr curve.proven_rank)
w=$(pyr curve.root_number)
gr=$(pyr fibration.generic_mordell_weil_rank)
sr=$(pyr fibration.special_fiber_rank)
rz=$(pyg twisted.zero_modes)
rg=$(pyg generic.zero_modes)
[ "$rank" = "29" ] && [ "$w" = "-1" ] && [ "$gr" = "17" ] && [ "$sr" = "29" ] && [ "$rg" = "17" ] && [ "$rz" = "29" ] && { echo CONSISTENT; exit 0; } || { echo INCONSISTENT "rank=$rank w=$w gr=$gr sr=$sr genus_generic=$rg genus_twisted=$rz"; exit 1; }
