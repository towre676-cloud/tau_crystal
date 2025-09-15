#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
envf="analysis/reciprocity_best.env"; out="analysis/padic_family.tsv"
[ -s "$envf" ] || envf="analysis/reciprocity_second.env"
[ -s "$envf" ] || { echo "[skip] no reciprocity env found"; exit 0; }
S0=$(read_kv "$envf" BEST_S_MICRO); T0=$(read_kv "$envf" BEST_T_MICRO)
: > "$out"; printf "%s\n" "weight\tS_micro\tT_micro" >> "$out"
for w in 2 4 6 8 10 12; do Sm=$(( S0 + (w-6)*1000 )); Tm=$(( T0 + (w-6)*500 )); printf "%s\n" "$w	$Sm	$Tm" >> "$out"; done
