#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
best="analysis/reciprocity_best.env"; sec="analysis/reciprocity_second.env"; scan="analysis/bash_theta_scan.tsv"
readv(){ f="$1"; k="$2"; awk -F= -v k="$k" '$1==k{gsub(/\r/,"",$2);print $2}' "$f" 2>/dev/null | head -n1; }
S1=$(readv "$best" BEST_S_MICRO); T1=$(readv "$best" BEST_T_MICRO)
S2=$(readv "$sec"  BEST_S_MICRO); T2=$(readv "$sec"  BEST_T_MICRO)
[ -n "$S1" ] && [ -n "$T1" ] && [ -n "$S2" ] && [ -n "$T2" ] || { echo "[line] skip: need best+second env"; exit 0; }
[ -s "$scan" ] || { echo "[line] skip: need $scan"; exit 0; }
STEPS=${ATLAS_STEPS:-101}; OUT="analysis/atlas_line.tsv"; SVG="analysis/plots/atlas_line.svg"
: > "$OUT"; printf "%s\n" "t\tS_micro\tT_micro\tdiff\tfound" >> "$OUT"
awk -F"\t" 'NR==1{next} {key=$1","$2; D[key]=$3} END{for(k in D) print k"\t"D[k]}' "$scan" | sort > analysis/.scan_index.tsv
for n in $(seq 0 $((STEPS-1))); do
  # linear interpolation in micro space
  num=$n; den=$((STEPS-1));
  Sm=$(( S1 + (S2 - S1) * num / den ))
  Tm=$(( T1 + (T2 - T1) * num / den ))
  key="${Sm},${Tm}"
  d=$(awk -F"\t" -v k="$key" '$1==k{print $2; exit}' analysis/.scan_index.tsv)
  if [ -n "$d" ]; then printf "%s\n" "$n	$Sm	$Tm	$d	1" >> "$OUT"; else printf "%s\n" "$n	$Sm	$Tm		0" >> "$OUT"; fi
done
: > "$SVG"; printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1200\" height=\"400\"><rect width=\"1200\" height=\"400\" fill=\"white\"/>" >> "$SVG"
awk -F"\t" 'NR==1{next} {if($5==1){x[NR]=$1; y[NR]=$4; if(minY==""||$4<minY)minY=$4; if($4>maxY)maxY=$4; if($1>maxX)maxX=$1}} END{if(maxY==""){print "</svg>" > "/dev/stderr"; exit} for(i=2;i<=NR;i++){if(y[i]=="")continue; xs=(maxX==0?0:(x[i]/maxX)); ys=((maxY==minY)?0.5: (y[i]-minY)/(maxY-minY)); X=int(50+xs*1100); Y=int(350-ys*300); print "<circle cx=\""X"\" cy=\""Y"\" r=\"3\" fill=\"#1f77b4\"/>"}}' "$OUT" >> "$SVG"
printf "%s\n" "</svg>" >> "$SVG"; echo "[line] wrote $OUT and $SVG"
