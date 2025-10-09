#!/usr/bin/env bash
. "./scripts/meta/../safe/_env.sh"
set -e
cd "/c/Users/Cody/Desktop/tau_crystal/tau_crystal" || exit 1
JR="receipts/k3_next_receipt.json"; JG="receipts/genus/k3_next_observation.json"
[ -s "receipts/k3_next_receipt.json" ] && [ -s "receipts/genus/k3_next_observation.json" ] || { echo missing receipts >&2; exit 2; }
pyr(){ python scripts/safe/json_read.py "$1" "$JR"; }
pyg(){ python scripts/safe/json_read.py "$1" "$JG"; }
rz=$(pyg twisted.zero_modes); rg=$(pyg generic.zero_modes); w=$(pyr curve.root_number)
[ "$w" = "-1" ] && [ -n "$rz" ] && [ -n "$rg" ] && [ "$rz" -gt "$rg" ] && { echo CONSISTENT; exit 0; } || { echo INCONSISTENT "w=$w generic=$rg twisted=$rz"; exit 1; }
