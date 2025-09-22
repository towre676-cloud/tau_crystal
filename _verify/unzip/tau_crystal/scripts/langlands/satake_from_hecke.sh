#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1
IN="analysis/hecke.tsv"; OUT="analysis/satake_angles.tsv"
[ -s "$IN" ] || { echo "[satake] missing $IN"; exit 2; }
awk -F"\t" 'BEGIN{OFS="\t"} NR==1 && ($1 ~ /p/i && $2 ~ /a/i){next} {p=$1+0; ap=$2+0; b=2*sqrt(p); x=ap/b; if(x>1)x=1; if(x<-1)x=-1; t=acos(x); print p,t}' "$IN" > "$OUT"
echo -e "p\ttheta" | cat - "$OUT" > "$OUT.tmp" && mv "$OUT.tmp" "$OUT"
