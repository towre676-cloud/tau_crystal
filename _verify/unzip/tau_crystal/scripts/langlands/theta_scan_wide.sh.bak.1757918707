#!/usr/bin/env bash
set -Eeuo pipefail; set +H

. scripts/langlands/_bash_math.sh
. scripts/langlands/minimal_tau.sh

A="${1:?usage: theta_scan_wide.sh <dirA> <dirB> [out.tsv] }"
B="${2:?}"
OUT="${3:-analysis/bash_theta_scan.tsv}"

mkdir -p "$(dirname "$OUT")"
: > "$OUT"
printf "%s\n" "S_micro\tT_micro\tdiff\tmA\tmB\tnA\tnB" >> "$OUT"

# Hecke-mean of A once (no process substitution)
set -- $(dir_signature hecke "$A")
sA="${1:-0}"; nA="${2:-0}"
[ "$nA" -gt 0 ] || nA=1
mA=$(( sA / nA ))

# Grid (micro-units). Env-configurable defaults:
S_MIN=${S_MIN:-500000}
S_MAX=${S_MAX:-1200000}
S_STEP=${S_STEP:-20000}
T_MIN=${T_MIN:-0}
T_MAX=${T_MAX:-150000}
T_STEP=${T_STEP:-5000}

S=$S_MIN
while [ "$S" -le "$S_MAX" ]; do
  T=$T_MIN
  while [ "$T" -le "$T_MAX" ]; do
    set -- $(dir_signature theta "$B" "$S" "$T")
    sB="${1:-0}"; nB="${2:-0}"
    [ "$nB" -gt 0 ] || nB=1
    mB=$(( sB / nB ))
    d=$(( mA>mB ? mA-mB : mB-mA ))
    printf "%d\t%d\t%d\t%d\t%d\t%d\t%d\n" "$S" "$T" "$d" "$mA" "$mB" "$nA" "$nB" >> "$OUT"
    T=$(( T + T_STEP ))
  done
  S=$(( S + S_STEP ))
done

echo "$OUT"
