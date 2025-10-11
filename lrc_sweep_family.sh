#!/usr/bin/env sh
# Usage: ./lrc_sweep_family.sh Kmin Kmax > family.csv
# CSV header:
echo "N,k,a_list,s_num,s_den,max_num,max_den,OK"
KMIN="${1:-2}"
KMAX="${2:-12}"
for k in $(awk -v a="$KMIN" -v b="$KMAX" 'BEGIN{for(i=a;i<=b;i++)print i}'); do
  N=$((k+1))
  A=""
  for i in $(awk -v k="$k" 'BEGIN{for(j=1;j<=k;j++)print j}'); do
    A="$A $i"
  done
  ./lrc_csv.sh "$N" $A
done
