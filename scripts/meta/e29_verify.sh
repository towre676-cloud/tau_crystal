#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
g1=$(grep -F "proven_rank: 29"           e29_curve_data.txt      || true)
g2=$(grep -F "generic_mordell_weil_rank"  k3_fibration_structure.txt || true)
g3=$(grep -F "root_number: -1"            e29_root_number.txt     || true)
[ -n "$g1" ] && [ -n "$g2" ] && [ -n "$g3" ] && { echo PASS; exit 0; } || { echo FAIL; exit 1; }
