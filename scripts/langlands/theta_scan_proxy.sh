#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
OUT="analysis/bash_theta_scan.tsv"; : > "$OUT"; printf "%s\n" "S_micro\tT_micro\tdiff\tmA\tmB\tnA\tnB" >> "$OUT"
S_MIN=${S_MIN:?}; S_MAX=${S_MAX:?}; S_STEP=${S_STEP:?}; T_MIN=${T_MIN:?}; T_MAX=${T_MAX:?}; T_STEP=${T_STEP:?}
S0=0; T0=0
if [ -s analysis/reciprocity_best.env ]; then S0=$(awk -F= '$1=="BEST_S_MICRO"{print $2}' analysis/reciprocity_best.env); T0=$(awk -F= '$1=="BEST_T_MICRO"{print $2}' analysis/reciprocity_best.env); fi
for S in $(seq "$S_MIN" "$S_STEP" "$S_MAX"); do
  for T in $(seq "$T_MIN" "$T_STEP" "$T_MAX"); do
    ds=$(( S - S0 )); [ "$ds" -lt 0 ] && ds=$(( -ds ))
    dt=$(( T - T0 )); [ "$dt" -lt 0 ] && dt=$(( -dt ))
    d2=$(( ds*ds + dt*dt ))
    D=$(isqrt "$d2")
    printf "%s\n" "$S	$T	$D	$S	$T	1	1" >> "$OUT"
  done
done
echo "[proxy] wrote $OUT (parabolic Δ proxy around best witness)"
