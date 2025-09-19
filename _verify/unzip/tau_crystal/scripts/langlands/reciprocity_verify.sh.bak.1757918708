#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/langlands/minimal_tau.sh
. analysis/reciprocity_best.env
TOL="${1:-1000}"; A="${2:-.tau_ledger}"; B="${3:-.tau_ledger/demo}"
set -- $(dir_signature hecke "$A"); sA=$1; nA=$2; [ "$nA" -gt 0 ] || nA=1; mA=$(( sA/nA ))
set -- $(dir_signature theta "$B" "$BEST_S_MICRO" "$BEST_T_MICRO"); sB=$1; nB=$2; [ "$nB" -gt 0 ] || nB=1; mB=$(( sB/nB ))
D=$(( mA>mB ? mA-mB : mB-mA ))
printf "verify: Sµ=%s Tµ=%s  mA=%d mB=%d  Δ=%dµ  (tol=%dµ)\n" "$BEST_S_MICRO" "$BEST_T_MICRO" "$mA" "$mB" "$D" "$TOL"
[ "$D" -le "$TOL" ] && { echo "[ok] reciprocity within tol"; exit 0; }
echo "[fail] reciprocity outside tol"; exit 1
