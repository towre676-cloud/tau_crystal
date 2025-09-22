#!/usr/bin/env bash
set -Ee -o pipefail; set +H
. scripts/langlands/minimal_tau.sh
A="${1:-.tau_ledger}"; B="${2:-.tau_ledger/demo}"; S="${3:?S_micro}"; T="${4:?T_micro}"
OUT="${5:-analysis/bash_theta_scan.tsv}"
mkdir -p "$(dirname "$OUT")"
[ -s "$OUT" ] || printf "%s\n" "S_micro\tT_micro\tdiff\tmA\tmB\tnA\tnB" > "$OUT"
set -- $(dir_signature hecke "$A"); sA=$1; nA=$2; [ "$nA" -gt 0 ] || nA=1; mA=$(( sA/nA ))
set -- $(dir_signature theta "$B" "$S" "$T"); sB=$1; nB=$2; [ "$nB" -gt 0 ] || nB=1; mB=$(( sB/nB ))
D=$(( mA>mB ? mA-mB : mB-mA ))
printf "%d\t%d\t%d\t%d\t%d\t%d\t%d\n" "$S" "$T" "$D" "$mA" "$mB" "$nA" "$nB" | tee -a "$OUT"
