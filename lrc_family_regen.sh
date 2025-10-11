#!/usr/bin/env sh
# Usage: ./lrc_family_regen.sh Kmin Kmax
OUT="lrc_family_results.csv"
: > "$OUT"
echo "N,k,a_list,s_num,s_den,max_num,max_den,OK" >> "$OUT"
KMIN="${1:-2}"; KMAX="${2:-12}"
for k in $(awk -v a="$KMIN" -v b="$KMAX" 'BEGIN{for(i=a;i<=b;i++)print i}'); do
  N=$((k+1))
  A=""; for j in $(awk -v k="$k" 'BEGIN{for(i=1;i<=k;i++)print i}'); do A="$A $j"; done
  ./lrc_csv.sh "$N" $A >> "$OUT"
done
printf "wrote %s (%s lines)\n" "$OUT" "$(wc -l < "$OUT")"
