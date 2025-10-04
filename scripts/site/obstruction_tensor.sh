#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cijk="${1:-artifacts/site/cover_cocycles.tsv}"
res="${2:-artifacts/residue/zeta_residue.tsv}"
out="${3:-artifacts/site/obstruction.tsv}"
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
if [ ! -f "$cijk" ] || [ ! -f "$res" ]; then echo "[err] need cocycles and residue" >&2; exit 2; fi
K=$(awk 'NR==2{print $2+0}' "$res")
awk -v K="$K" 'NR>1{obs=$4 - K; printf "%d\t%d\t%d\t%.9f\n",$1,$2,$3,obs}' "$cijk" > "$tmp"
printf "i\tj\tk\tObs\n" > "$out"
cat "$tmp" >> "$out"
echo "[ok] obstruction tensor -> $out"
