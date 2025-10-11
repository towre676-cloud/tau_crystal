#!/usr/bin/env sh
# Usage: ./lrc_random_batch_both.sh T Nmin Nmax Kmin Kmax > out.csv
T="${1:-25}"; NMIN="${2:-5}"; NMAX="${3:-40}"; KMIN="${4:-2}"; KMAX="${5:-8}"

HEADER=1 ./lrc_csv_both.sh 1 1 >/dev/null 2>&1  # noop to warm env var usage
echo "N,k,a_list,cont_s_num,cont_s_den,cont_max_num,cont_max_den,cont_OK,disc_s_num,disc_s_den,disc_max_num,disc_max_den,disc_OK,s_den_divides_N,agree_max"

i=0
while [ "$i" -lt "$T" ]; do
  N=$(awk -v a="$NMIN" -v b="$NMAX" 'BEGIN{srand(); print int(a+rand()*(b-a+1))}')
  K=$(awk -v a="$KMIN" -v b="$KMAX" 'BEGIN{srand(); print int(a+rand()*(b-a+1))}')
  [ "$K" -ge "$N" ] && continue  # need K ≤ N-1
  A=$(seq 1 $((N-1)) | awk 'BEGIN{srand()} {print rand(),$0}' | sort -k1,1n | awk '{print $2}' | head -n "$K" | xargs)
  HEADER=0 ./lrc_csv_both.sh "$N" $A
  i=$((i+1))
done
