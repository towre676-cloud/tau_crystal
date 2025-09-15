#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
in="${1:-analysis/double_zero_ords.tsv}"; out="analysis/feq_report.txt"; eps="${FEQ_EPS_MICRO:-10}"
: > "$out"; [ -s "$in" ] || { echo "[feq] skip: $in missing" | tee -a "$out"; exit 0; }
tmp="$(mktemp)";
case "$in" in *.tsv) awk "NR>1{print \$2}" "$in" > "$tmp";; *.json) tr -d "\r\n\t " < "$in" | sed "s/[][]/\n/g;s/,/\n/g" | awk "NF{print}" > "$tmp";; *) cp "$in" "$tmp";; esac
N=$(wc -l < "$tmp" | tr -d "[:space:]"); [ "$N" -eq 0 ] && { echo "[feq] no ordinates" | tee -a "$out"; rm -f "$tmp"; exit 0; }
mn=$(awk "NR==1{x=\$1;mx=\$1} NR>1{if(\$1<x)x=\$1;if(\$1>mx)mx=\$1} END{print x}" "$tmp"); mx=$(awk "NR==1{x=\$1;mx=\$1} NR>1{if(\$1<x)x=\$1;if(\$1>mx)mx=\$1} END{print mx}" "$tmp")
center=0; target_sum=0
[ "$mn" -ge 0 ] && [ "$mx" -le 1000000 ] && { center=500000; target_sum=1000000; }
printf "%s\n" "Functional Equation Proxy Report" >> "$out"
printf "%s\n" "UTC: $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$out"
printf "%s\n\n" "center_micro=$center  eps=$eps" >> "$out"
awk -v C="$center" -v SUM="$target_sum" -v EPS="$eps" '{a[NR]=$1} END{paired=0; unp=0; usedc=0; for(i=1;i<=NR;i++){if(u[i])continue; xi=a[i]; found=0; for(j=i+1;j<=NR;j++){if(u[j])continue; xj=a[j]; if(SUM){ if((xi+xj>=SUM-EPS)&&(xi+xj<=SUM+EPS)){u[i]=u[j]=1; paired++; found=1; break} } else { if((xi>=-xj-EPS)&&(xi<=-xj+EPS)){u[i]=u[j]=1; paired++; found=1; break} } } if(!found){unp++} } print "pairs:",paired >> F; print "unpaired:",unp >> F}' F="$out" "$tmp"
rm -f "$tmp"; echo "[feq] wrote $out"
