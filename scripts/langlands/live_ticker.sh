#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
scan="analysis/bash_theta_scan.tsv"; morse="analysis/morse_crit.tsv"
printf "%s\n" "[ticker] watching $scan (Ctrl-C to stop)"
while :; do
  if [ -f "$scan" ]; then rows="$(wc -l < "$scan" 2>/dev/null || echo 0)"; else rows=0; fi
  # data rows exclude header
  if [ "$rows" -gt 0 ]; then data=$((rows-1)); else data=0; fi
  best="$(awk -F\"\t\" 'NR>1{ if(min==""||$3<min){min=$3;s=$1;t=$2} } END{ if(min!="") printf("Δ=%s @ S=%s T=%s",min,s,t) }' "$scan" 2>/dev/null)"
  mins="$(awk -F\"\t\" '$4=="min"{c++} END{print (c?c:0)}' "$morse" 2>/dev/null)"
  now="$(date +%H:%M:%S)"
  printf "\r[%s] rows=%-8s minima=%-4s %s   " "$now" "$data" "$mins" "$best"
  sleep 1
done
