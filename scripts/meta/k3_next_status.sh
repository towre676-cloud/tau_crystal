#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
JR="receipts/k3_next_receipt.json"; JG="receipts/genus/k3_next_observation.json"
pyr(){ python scripts/safe/json_read.py "$1" "$JR"; }
pyg(){ python scripts/safe/json_read.py "$1" "$JG"; }
echo "— k3_next STATUS —"
echo "a4:   $(pyr curve.a4)"
echo "a6:   $(pyr curve.a6)"
echo "disc: $(pyr curve.discriminant_sign)"
echo "w:    $(pyr curve.root_number)"
echo "genus zero-modes: generic=$(pyg generic.zero_modes) → twisted=$(pyg twisted.zero_modes)"
echo "fib ranks:          generic=$(pyr fibration.generic_mordell_weil_rank) → special=$(pyr fibration.special_fiber_rank)"
echo "regulator det:      $(pyr curve.regulator_det)"
echo "height matrix size: $(pyr height_matrix_size)"
