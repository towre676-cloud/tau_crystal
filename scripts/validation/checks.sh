#!/usr/bin/env bash
set -euo pipefail; set +H; . scripts/validation/_util.sh
AP="$1"; AN="$2"; AP2="$3"
awk -F"\t" '{if($2 !~ /^-?[0-9]+$/){print "NONINT p="$1" v="$2 > "/dev/stderr"; ok=0}} END{exit ok?0:1}' ok=1 "$AP"
while read -r p a; do
  thr=$(awk -v p="$p" 'BEGIN{printf("%.6f",2*sqrt(p))}')
  abs=$(( a<0?-a:a ))
  awk -v A="$abs" -v T="$thr" 'BEGIN{exit (A<=T)?0:1}' || { echo "RAM_FAIL p="$p" a="$a" thr="$thr >&2; exit 1; }
done < "$AP"
declare -A ANV; while read -r n a; do ANV[$n]=$a; done < "$AN"
for ((m=2;m<=50;m++)); do for ((n=2;n<=50;n++)); do mn=$((m*n)); if [ $mn -le 1000 ]; then g=$(gcd $m $n); if [ $g -eq 1 ]; then am=${ANV[$m]:-0}; an=${ANV[$n]:-0}; amn=${ANV[$mn]:-999999999}; [ $((am*an)) -eq $amn ] || { echo "MULT_FAIL m="$m" n="$n >&2; exit 1; }; fi; fi; done; done
join -t "	" -j1 <(sort -n "$AP") <(sort -n "$AP2") | awk -F"\t" '{if($2!=$3){print "STAB_FAIL p="$1" a1="$2" a2="$3 > "/dev/stderr"; exit 1}}'
