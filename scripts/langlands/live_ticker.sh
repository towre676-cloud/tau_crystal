#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
scan="analysis/bash_theta_scan.tsv"
morse="analysis/morse_crit.tsv"
printf "%s\n" "[ticker] watching $scan (Ctrl-C to stop)"
while :; do
  rows=0
  [ -f "$scan" ] && rows="$(wc -l < "$scan" 2>/dev/null || echo 0)"
  data=$(( rows>0 ? rows-1 : 0 ))
  # best Δ from scan
  best=""
  if [ "$data" -gt 0 ]; then
    min=""; bs=""; bt=""
    first=1
    # shellcheck disable=SC2162
    while IFS=$'\t' read s t d _; do
      if [ "$first" = 1 ]; then first=0; case "$s" in ''|*[!0-9-]* ) continue;; esac; fi
      case "$d" in ''|*[!0-9-]* ) continue;; esac
      if [ -z "$min" ] || [ "$d" -lt "$min" ]; then min="$d"; bs="$s"; bt="$t"; fi
    done < "$scan"
    [ -n "$min" ] && best="Δ=$min @ S=$bs T=$bt"
  fi
  # minima from morse (type starts with 'min')
  mins=0
  if [ -s "$morse" ]; then
    first=1
    # shellcheck disable=SC2162
    while IFS=$'\t' read s t typ _rest; do
      if [ "$first" = 1 ]; then first=0; case "$s" in ''|*[!0-9-]* ) continue;; esac; fi
      case "$typ" in min*|Min*|MIN*) mins=$((mins+1));; esac
    done < "$morse"
  fi
  now="$(date +%H:%M:%S)"
  printf "\r[%s] rows=%-6s minima=%-4s %s   " "$now" "$data" "$mins" "$best"
  sleep 1
done
