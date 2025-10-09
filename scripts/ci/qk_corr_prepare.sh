#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
IN="${1:-./tmp/qk_corr.txt}"; OUT="./tmp/qk_corr.norm.tsv"; mkdir -p ./tmp
[ -f "$IN" ] || { echo "[err] missing: $IN" >&2; exit 2; }
tr -d "\r" < "$IN" | awk -v OFS="\t" 'NF==2{print NR-1,$1,$2} NF>=3{print $1,$2,$3}' > "$OUT"
echo "[prep] $(wc -l < "$OUT") rows -> $OUT"
