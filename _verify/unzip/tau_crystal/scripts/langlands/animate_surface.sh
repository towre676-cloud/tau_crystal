#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022

jitter_second() {
  f="analysis/reciprocity_second.env"
  S2="$(sed -n 's/^BEST_S_MICRO=\(.*\)$/\1/p' "$f" 2>/dev/null | head -n1)"
  T2="$(sed -n 's/^BEST_T_MICRO=\(.*\)$/\1/p' "$f" 2>/dev/null | head -n1)"
  : "${S2:=314000}"; : "${T2:=-176000}"
  J=$((RANDOM%8001)); K=$((RANDOM%8001))
  S2n=$(( S2 + 4000 - J ))
  T2n=$(( T2 + 4000 - K ))
  printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n" "$S2n" "$T2n" > "$f"
}

rowcount() { f="$1"; if [ -f "$f" ]; then n="$(wc -l < "$f" 2>/dev/null)" || n=""; if [ -z "$n" ]; then c=0; while IFS= read -r _; do c=$((c+1)); done < "$f"; echo "$c"; else echo "$n"; fi; else echo 0; fi; }

while :; do
  # nudge the second witness so basins can move
  jitter_second

  # sweep coarse -> fine
  for PAD in 70000 50000 30000; do
    for STEP in 3000 2000 1000; do
      S_PAD=$PAD T_PAD=$PAD S_STEP=$STEP T_STEP=$STEP \
      bash scripts/langlands/theta_scan_proxy2.sh

      bash scripts/langlands/morse2d_pure.sh analysis/bash_theta_scan.tsv
      bash scripts/langlands/basins_map.sh   || true
      bash scripts/langlands/atlas_line.sh   || true

      # stamp status
      ROWS=$(rowcount analysis/bash_theta_scan.tsv); ROWS=$(( ROWS>0 ? ROWS-1 : 0 ))
      echo "utc=$(date -u +%Y-%m-%dT%H:%M:%SZ) pad=$PAD step=$STEP rows=$ROWS" >> analysis/atlas_status.txt

      sleep 4
    done
  done
done
