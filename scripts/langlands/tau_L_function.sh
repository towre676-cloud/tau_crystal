#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
seqfile="${1:-.tau_ledger/seq/tau.csv}"; out=".tau_ledger/langlands/L_tau.json"
mkdir -p ".tau_ledger/langlands"
[ -s "$seqfile" ] || { echo "{\"status\":\"no_tau\",\"grid\":[0.8,0.9,1.0,1.1],\"L\":[],\"zeros\":[]}" > "$out"; echo "$out"; exit 0; }
tmp="$(mktemp)"; awk -F, "NR>1{print \$2}" "$seqfile" > "$tmp"
N=$(wc -l < "$tmp" | awk "{print \$1}")
[ "${N:-0}" -ge 8 ] || { echo "{\"status\":\"short\",\"grid\":[0.8,0.9,1.0,1.1],\"L\":[],\"zeros\":[]}" > "$out"; rm -f "$tmp"; echo "$out"; exit 0; }
SAMP="0.8 0.9 1.0 1.1 1.2 1.5 2.0"; lvals="";
for s in $SAMP; do
  L=$(awk -v s="$s" 'NR==1{prev=$1; next}{dn=$1-prev; prev=$1; n++; if(n>0){pw=exp(log(n)*s); term=(dn==0?0:dn)/(n*pw); sum+=term}} END{printf "%.8f", exp(sum+0)}' "$tmp")
  [ -z "$lvals" ] && lvals="$L" || lvals="$lvals,$L"
done
zeros=""; prevd=""; i=1; cnt=$(echo "$SAMP" | wc -w)
while [ $i -lt $cnt ]; do a=$(echo "$lvals" | tr "," "\n" | sed -n "${i}p"); b=$(echo "$lvals" | tr "," "\n" | sed -n "$((i+1))p");
  al=$(awk -v x="$a" "BEGIN{print log((x<=0)?1e-12:x)}"); bl=$(awk -v x="$b" "BEGIN{print log((x<=0)?1e-12:x)}"); d=$(awk -v A="$al" -v B="$bl" "BEGIN{print B-A}")
  if [ "$i" -gt 1 ]; then ch=$(awk -v p="$prevd" -v q="$d" "BEGIN{print (p*q<0)?1:0}"); if [ "$ch" = "1" ]; then sl=$(echo $SAMP | awk "{print \$'$i'}"); sr=$(echo $SAMP | awk "{print \$'$((i+1))'}"); [ -z "$zeros" ] && zeros="\"$sl-$sr\"" || zeros="$zeros,\"$sl-$sr\""; fi; fi
  prevd="$d"; i=$((i+1))
done
echo "{" > "$out"
echo "\"status\":\"ok\",\"grid\":[$(echo $SAMP | sed 's/ /,/g')],\"L\":[${lvals}],\"zeros\":[${zeros}]}" >> "$out"
rm -f "$tmp"; echo "$out"
