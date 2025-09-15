#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
scan="analysis/bash_theta_scan.tsv"
morse="analysis/morse_crit.tsv"

# In-place repaint disabled on Windows Git Bash (msys/cygwin)
inplace=1
case "${OSTYPE:-}" in msys*|cygwin*|win*) inplace=0 ;; esac

printf "%s\n" "[ticker] watching $scan (Ctrl-C to stop)"
while :; do
  rows=0
  [ -f "$scan" ] && rows="$(wc -l < "$scan" 2>/dev/null || echo 0)"
  data=$(( rows>0 ? rows-1 : 0 ))

  # best Δ (pure bash)
  best=""; min=""; bs=""; bt=""
  if [ "$data" -gt 0 ]; then
    first=1
    while IFS=$'\t' read -r s t d _rest; do
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
    while IFS=$'\t' read -r s t typ _rest; do
      if [ "$first" = 1 ]; then first=0; case "$s" in ''|*[!0-9-]* ) continue;; esac; fi
      case "$typ" in min*|Min*|MIN*) mins=$((mins+1));; esac
    done < "$morse"
  fi

  now="$(date +%H:%M:%S)"
  line="[$now] rows=$data minima=$mins $best"
  if [ "$inplace" -eq 1 ]; then
    printf "\r%s   " "$line"
  else
    printf "%s\n" "$line"
  fi
  sleep 1
done
