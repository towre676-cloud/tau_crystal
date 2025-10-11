#!/usr/bin/env bash
# Usage: ./lrc_random_batch.sh T Nmin Nmax kmin kmax > random_results.csv
# Emits header + T unique rows.

T="${1:-25}"; NMIN="${2:-5}"; NMAX="${3:-40}"; KMIN="${4:-2}"; KMAX="${5:-8}"

echo "N,k,a_list,s_num,s_den,max_num,max_den,OK"

# track uniqueness on (N|a_list)
declare -A seen
count=0

while (( count < T )); do
  N=$(( RANDOM % (NMAX - NMIN + 1) + NMIN ))
  maxK=$(( N - 1 ))
  (( maxK < KMIN )) && continue
  K=$(( RANDOM % (KMAX - KMIN + 1) + KMIN ))
  (( K > maxK )) && K=$maxK

  # build pool 1..N-1
  n=$(( N - 1 ))
  pool=()
  for (( i=1; i<=n; i++ )); do pool[i-1]=$i; done

  # Fisher–Yates shuffle
  for (( i=n-1; i>0; i-- )); do
    j=$(( RANDOM % (i + 1) ))
    tmp=${pool[i]}; pool[i]=${pool[j]}; pool[j]=$tmp
  done

  # take first K, sort ascending (robust, no process substitution)
  pick=( "${pool[@]:0:K}" )
  sorted_str="$(printf '%s\n' "${pick[@]}" | sort -n | tr '\n' ' ')"
  # to array
  read -r -a pick_sorted <<< "$sorted_str"

  a_list="${pick_sorted[*]}"
  key="${N}|${a_list}"
  [[ -n "${seen[$key]:-}" ]] && continue
  seen[$key]=1

  ./lrc_csv.sh "$N" "${pick_sorted[@]}"
  ((count++))
done
