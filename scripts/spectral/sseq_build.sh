#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
traces=".tau_ledger/seq/tau.csv"; svg=".tau_ledger/sseq/E_pages.svg"; mkdir -p "$(dirname "$svg")"
[ -s "$traces" ] || { echo "<svg xmlns=\\"http://www.w3.org/2000/svg\\" width=\\"640\\" height=\\"120\\"><text x=\\"10\\" y=\\"60\\">no tau.csv</text></svg>" > "$svg"; echo "$svg"; exit 0; }
tmp="$(mktemp)"; awk -F, "NR>1{print NR-1\",\"$2}" "$traces" > "$tmp"
n=$(wc -l < "$tmp"); [ "${n:-0}" -gt 0 ] || { echo "<svg xmlns=\\"http://www.w3.org/2000/svg\\" width=\\"640\\" height=\\"120\\"><text x=\\"10\\" y=\\"60\\">empty</text></svg>" > "$svg"; rm -f "$tmp"; echo "$svg"; exit 0; }
: > "$svg"
printf "%s\n" "<svg xmlns=\\"http://www.w3.org/2000/svg\\" width=\\"800\\" height=\\"240\\">" >> "$svg"
printf "%s\n" "<rect x=\\"0\\" y=\\"0\\" width=\\"800\\" height=\\"240\\" fill=\\"white\\"/>" >> "$svg"
scale(){ awk -v v="$1" -v a="$2" -v b="$3" -v A="$4" -v B="$5" "BEGIN{ if(b-a<1e-12){print A}else{print A+(v-a)*(B-A)/(b-a)} }"; }
min=$(awk -F, "NR==1{m=$2} NR>1{if($2<m)m=$2} END{print m}" "$tmp"); max=$(awk -F, "NR==1{M=$2} NR>1{if($2>M)M=$2} END{print M}" "$tmp")
awk -F, -v min="$min" -v max="$max" '{ x=$1; y=$2; X=50+ (x*3); Y=180 - (y-min)/(max-min+1e-12)*120; printf "<circle cx=\\"%.2f\\" cy=\\"%.2f\\" r=\\"1.5\\" />\n", X, Y }' "$tmp" >> "$svg"
printf "%s\n" "<text x=\\"50\\" y=\\"210\\">E1: instruction trace projection</text>" >> "$svg"
printf "%s\n" "<text x=\\"50\\" y=\\"225\\">E2/E3 heuristics available via windowed dispersion; see CEP and dim_τ.</text>" >> "$svg"
printf "%s\n" "</svg>" >> "$svg"
rm -f "$tmp"; echo "$svg"
