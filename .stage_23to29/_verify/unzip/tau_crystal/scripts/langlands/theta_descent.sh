#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/langlands/minimal_tau.sh
A="${1:-.tau_ledger}"; B="${2:-.tau_ledger/demo}"
S="${3:-320000}"; T="${4:-(-120000)}"
S_STEP="${5:-20000}"; T_STEP="${6:-10000}"
ROUNDS="${7:-20}"
clamp(){ v="$1"; lo="$2"; hi="$3"; [ "$v" -lt "$lo" ] && v="$lo"; [ "$v" -gt "$hi" ] && v="$hi"; printf "%d\n" "$v"; }
eval_m(){ set -- $(dir_signature hecke "$A"); sA=$1; nA=$2; [ "$nA" -gt 0 ] || nA=1; mA=$(( sA/nA )); set -- $(dir_signature theta "$B" "$1" "$2"); }
set -- $(dir_signature hecke "$A"); sA=$1; nA=$2; [ "$nA" -gt 0 ] || nA=1; mA=$(( sA/nA ))
probe(){ local s="$1" t="$2"; set -- $(dir_signature theta "$B" "$s" "$t"); sB=$1; nB=$2; [ "$nB" -gt 0 ] || nB=1; mB=$(( sB/nB )); printf "%d %d %d\n" "$s" "$t" $(( mA>mB ? mA-mB : mB-mA )); }
read _ _ bestD < <(probe "$S" "$T"); bestS="$S"; bestT="$T"
printf "start S=%d T=%d  mA=%d D=%d\n" "$S" "$T" "$mA" "$bestD"
r=0
while [ "$r" -lt "$ROUNDS" ]; do
  improved=0
  # four neighbors
  for cand in \\
    "$(clamp $((bestS - S_STEP)) 0 2000000) $bestT" \\
    "$(clamp $((bestS + S_STEP)) 0 2000000) $bestT" \\
    "$bestS $(clamp $((bestT - T_STEP)) -2000000 2000000)" \\
    "$bestS $(clamp $((bestT + T_STEP)) -2000000 2000000)"
  do
    set -- $cand; s="$1"; t="$2"; read _ _ d < <(probe "$s" "$t")
    if [ "$d" -lt "$bestD" ]; then bestD="$d"; bestS="$s"; bestT="$t"; improved=1; fi
  done
  printf "round=%d  S=%d T=%d  D=%d\n" "$r" "$bestS" "$bestT" "$bestD"
  if [ "$improved" -eq 0 ]; then
    S_STEP=$(( S_STEP/2 )); T_STEP=$(( T_STEP/2 ))
    [ "$S_STEP" -gt 0 ] || S_STEP=1; [ "$T_STEP" -gt 0 ] || T_STEP=1
  fi
  r=$((r+1))
done
printf "best S=%d T=%d  D=%d\n" "$bestS" "$bestT" "$bestD"
