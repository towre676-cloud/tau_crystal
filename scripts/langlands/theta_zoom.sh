#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/langlands/minimal_tau.sh
A="${1:-.tau_ledger}"; B="${2:-.tau_ledger/demo}"
S="${3:-500000}"; T="${4:-0}"
S_STEP="${5:-20000}"; T_STEP="${6:-5000}"
ROUNDS="${7:-6}"
score(){ set -- $(dir_signature hecke "$A"); sA=$1; nA=$2; [ "$nA" -gt 0 ] || nA=1; mA=$(( sA/nA )); set -- $(dir_signature theta "$B" "$1" "$2"); }
bestS=$S; bestT=$T
set -- $(dir_signature hecke "$A"); sA=$1; nA=$2; [ "$nA" -gt 0 ] || nA=1; mA=$(( sA/nA ))
# eval current best
set -- $(dir_signature theta "$B" "$bestS" "$bestT"); sB=$1; nB=$2; [ "$nB" -gt 0 ] || nB=1; mB=$(( sB/nB )); bestD=$(( mA>mB ? mA-mB : mB-mA ))
printf "start S=%d T=%d  mA=%d mB=%d D=%d\n" "$bestS" "$bestT" "$mA" "$mB" "$bestD"
r=0
while [ "$r" -lt "$ROUNDS" ]; do
  improved=0
  for s in "$bestS" $((bestS - S_STEP)) $((bestS + S_STEP)); do
    for t in "$bestT" $((bestT - T_STEP)) $((bestT + T_STEP)); do
      set -- $(dir_signature theta "$B" "$s" "$t"); sB=$1; nB=$2; [ "$nB" -gt 0 ] || nB=1; mB=$(( sB/nB ))
      D=$(( mA>mB ? mA-mB : mB-mA ))
      if [ "$D" -lt "$bestD" ]; then bestD=$D; bestS=$s; bestT=$t; improved=1; fi
    done
  done
  printf "round=%d  S=%d T=%d  D=%d\n" "$r" "$bestS" "$bestT" "$bestD"
  [ "$improved" -eq 1 ] || { S_STEP=$(( S_STEP/2 )); T_STEP=$(( T_STEP/2 )); [ "$S_STEP" -gt 0 ] || S_STEP=1; [ "$T_STEP" -gt 0 ] || T_STEP=1; r=$((r+1)); continue; }
  r=$((r+1))
done
printf "best S=%d T=%d  D=%d\n" "$bestS" "$bestT" "$bestD"
