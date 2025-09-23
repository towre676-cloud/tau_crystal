#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/langlands/minimal_tau.sh
. analysis/reciprocity_best.env

TOL="${1:-1000}"
A="${2:-.tau_ledger}"
B="${3:-.tau_ledger/demo}"

# A-side mean: classic hecke or hecke2 when A_OP=hecke2
if [ "${A_OP:-hecke}" = "hecke2" ]; then
  set -- $(scripts/langlands/hecke2_mean.sh "$A"); sA=$1; nA=$2
else
  set -- $(dir_signature hecke "$A"); sA=$1; nA=$2
fi
[ "${nA:-0}" -gt 0 ] || nA=1
mA=$(( sA / nA ))

# B-side theta at frozen best (unchanged)
set -- $(dir_signature theta "$B" "$BEST_S_MICRO" "$BEST_T_MICRO"); sB=$1; nB=$2
[ "${nB:-0}" -gt 0 ] || nB=1
mB=$(( sB / nB ))

D=$(( mA>mB ? mA-mB : mB-mA ))
printf "verify[%s]: Sµ=%s Tµ=%s  mA=%d mB=%d  Δ=%dµ  (tol=%dµ)\n" "${A_OP:-hecke}" "$BEST_S_MICRO" "$BEST_T_MICRO" "$mA" "$mB" "$D" "$TOL"
[ "$D" -le "$TOL" ] && { echo "[ok] reciprocity within tol"; exit 0; }
echo "[fail] reciprocity outside tol"; exit 1
