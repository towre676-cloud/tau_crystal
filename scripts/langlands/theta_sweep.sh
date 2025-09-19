#!/usr/bin/env bash
set -E -o pipefail; set +H
A="${1:-.tau_ledger}"; B="${2:-.tau_ledger/demo}"; S="${3:-1000000}"
T_MIN="${4:-(-200000)}"; T_MAX="${5:-200000}"; T_STEP="${6:-5000}"
OUT="${7:-analysis/theta_sweep.tsv}"

mkdir -p "$(dirname "$OUT")"
: > "$OUT"; printf '%s\n' "T_micro	mA_micro	mB_micro	diff_micro	nA	nB" >> "$OUT"

set -- $(scripts/langlands/sig.sh hecke "$A"); sA=${1:-0}; nA=${2:-0}; [ "$nA" -gt 0 ] || nA=1
mA=$(( sA / nA ))

T="$T_MIN"; [ "$T_STEP" -lt 0 ] && T_STEP=$(( -T_STEP ))
while :; do
  set -- $(scripts/langlands/sig.sh theta "$B" "$S" "$T"); sB=${1:-0}; nB=${2:-0}; [ "$nB" -gt 0 ] || nB=1
  mB=$(( sB / nB ))
  D=$(( mB - mA )); [ "$D" -lt 0 ] && D=$(( -D ))
  printf "%d\t%d\t%d\t%d\t%d\t%d\n" "$T" "$mA" "$mB" "$D" "$nA" "$nB" >> "$OUT"
  printf "\rT=%d  mA=%d  mB=%d  |Δ|=%d   " "$T" "$mA" "$mB" "$D" 1>&2
  [ "$T" -ge "$T_MAX" ] && break
  T=$(( T + T_STEP ))
done
printf "\n" 1>&2
echo "$OUT"
