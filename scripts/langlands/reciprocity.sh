#!/usr/bin/env bash
set -Ee -o pipefail; set +H
. scripts/langlands/_bash_math.sh
. scripts/langlands/minimal_tau.sh
A="${1:-.tau_ledger}"; B="${2:-.tau_ledger/demo}"; TOL="${3:-1000}"
SOFT=0; [ "${4:-}" = "--soft" ] && SOFT=1
scan="$(bash scripts/langlands/theta_scan_wide.sh "$A" "$B" "analysis/bash_theta_scan.tsv")"
bestd=999999999; bestS=""; bestT=""; bestmA=""; bestmB=""; bestnA=""; bestnB=""
exec 9<"$scan"; IFS= read -r _hdr <&9 || true
while IFS= read -r line <&9; do
  [ -z "${line:-}" ] && continue
  first="${line%%[ 	]*}"; case "$first" in S_micro*|"#"*) continue;; esac
  set -- $line
  S="${1:-}"; T="${2:-0}"; D="${3:-}"; mA="${4:-0}"; mB="${5:-0}"; nA="${6:-0}"; nB="${7:-0}"
  [ -z "$S" ] || [ -z "$D" ] && continue
  S=$(( S + 0 )); T=$(( T + 0 )); D=$(( D + 0 ))
  mA=$(( mA + 0 )); mB=$(( mB + 0 )); nA=$(( nA + 0 )); nB=$(( nB + 0 ))
  if [ "$D" -lt "$bestd" ]; then bestd="$D"; bestS="$S"; bestT="$T"; bestmA="$mA"; bestmB="$mB"; bestnA="$nA"; bestnB="$nB"; fi
done; exec 9<&-
printf "best_diff_micro=%s\tS=%s\tT=%s\tmA=%s\tmB=%s\tnA=%s\tnB=%s\n" "$bestd" "$bestS" "$bestT" "$bestmA" "$bestmB" "$bestnA" "$bestnB"
if [ "$bestd" -le "$TOL" ]; then echo "[ok] reciprocity within tol"; exit 0; fi
echo "[fail] reciprocity outside tol"; [ "$SOFT" -eq 1 ] && exit 0 || exit 1
