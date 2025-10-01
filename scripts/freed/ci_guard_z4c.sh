#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
J=$(printf "%s\n" .tau_ledger/freed/z4c_resstudy_*.json | LC_ALL=C sort | tail -n1)
[ -f "$J" ] || { echo "[err] no z4c_resstudy JSON"; exit 1; }

stable=$(jq -r '.stable' "$J")
[ "$stable" = "true" ] || { echo "[fail] resstudy not stable"; jq '.stable,.deltas' "$J"; exit 2; }

neg=$(jq -r '[.deltas[] | select(.H<0 and .M<0 and ."C_Gamma"<0)] | length' "$J")
tot=$(jq -r '[.deltas[]]|length' "$J")
[ "$neg" = "$tot" ] || { echo "[fail] delta not <0 at all resolutions"; jq '.deltas' "$J"; exit 3; }

echo "[ok] Z4c guard: stable=true and all deltas < 0"
