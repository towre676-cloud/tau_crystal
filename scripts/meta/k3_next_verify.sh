#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
JR="receipts/k3_next_receipt.json"
JG="receipts/genus/k3_next_observation.json"
[ -s "$JR" ] && [ -s "$JG" ] || { echo "missing receipts" >&2; exit 2; }
pyr(){ python scripts/safe/json_read.py "$1" "$JR"; }
pyg(){ python scripts/safe/json_read.py "$1" "$JG"; }
gr_a=$(pyr fibration.generic_mordell_weil_rank)
sr_a=$(pyr fibration.special_fiber_rank)
rj_a=$(pyr fibration.rank_increase)
gr_g=$(pyg generic.zero_modes)
sr_g=$(pyg twisted.zero_modes)
[ "$gr_a" = "$gr_g" ] && [ "$sr_a" = "$sr_g" ] && [ "$rj_a" = "$(( sr_g - gr_g ))" ] && { echo PASS; exit 0; } || { echo FAIL "arith:($gr_a,$sr_a,$rj_a) genus:($gr_g,$sr_g,$(( sr_g - gr_g )))"; exit 1; }
