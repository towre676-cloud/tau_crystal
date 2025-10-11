#!/usr/bin/env sh
# Usage: ./lrc_random_batch_discrete.sh T Nmin Nmax Kmin Kmax > out.csv
# Picks T random instances with distinct a_i ∈ {1,..,N-1}, evaluates DISCRETE solver.

echo "N,k,a_list,s_num,s_den,max_num,max_den,OK"
T="${1:-25}"; NMIN="${2:-5}"; NMAX="${3:-40}"; KMIN="${4:-2}"; KMAX="${5:-8}"

i=0
while [ "$i" -lt "$T" ]; do
  N=$(awk -v a="$NMIN" -v b="$NMAX" 'BEGIN{srand(); print int(a+rand()*(b-a+1))}')
  K=$(awk -v a="$KMIN" -v b="$KMAX" 'BEGIN{srand(); print int(a+rand()*(b-a+1))}')
  [ "$K" -ge "$N" ] && continue  # need K ≤ N-1 for distinct a_i
  # sample K distinct a_i from 1..N-1
  A=$(seq 1 $((N-1)) | awk 'BEGIN{srand()} {print rand(),$0}' | sort -k1,1n | awk 'NR>0{print $2}' | head -n "$K" | xargs)
  ./lrc_csv_discrete.sh "$N" $A
  i=$((i+1))
done
