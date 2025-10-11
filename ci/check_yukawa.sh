#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
v=$(sed -n 's/.*"v"[[:space:]]*:[[:space:]]*\([0-9.eE+-]\+\).*/\1/p' tau_crystal/data/pdg/constants.json | tail -1)
sv=$(head -1 obstruction_card/out/singular_values_M.csv 2>/dev/null | sed "s/\r$//")
[ -n "${v:-}" ] && [ -n "${sv:-}" ] || { echo "-- Yukawa: missing v or singular_values_M.csv"; exit 0; }
echo "-- Yukawa mass spectrum m_i = sigma_i * v  (v=$v) --"
awk -v v="$v" -F, 'NR==1{
  for(i=1;i<=NF;i++){
    gsub(/^[[:space:]]+|[[:space:]]+$/,"",$i); sig=$i+0; m=sig*v;
    printf("  i=%d  sigma=%s  m=%.8f\n", i, $i, m)
  }
}' <(printf "%s\n" "$sv")
