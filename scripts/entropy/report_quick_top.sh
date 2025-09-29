#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -eu; umask 022; export LC_ALL=C LANG=C

CSV="analysis/entropy/witness_quick.csv"
N="${1:-20}"

[ -s "$CSV" ] || { echo "[err] missing CSV: $CSV (run: make entropy-quick)"; exit 2; }

# columns: file,bytes,sampled,sample_bytes,gz1_bytes,cr_gz1
# print header + top-N by cr_gz1 desc, with a simple fixed-width table
{
  echo "Top $N by cr_gz1 (higher = more compressible)"
  printf "%-6s  %-8s  %-8s  %-10s  %-8s  %s\n" "RANK" "cr_gz1" "bytes" "sample_b" "gz1_b" "file"
  tail -n +2 "$CSV" \
  | awk -F, 'NF>=6 && $6 ~ /^[0-9.]+$/ {printf "%.6f,%s,%s,%s,%s\n", $6,$2,$4,$5,$1}' \
  | LC_ALL=C sort -t, -k1,1nr \
  | head -n "$N" \
  | awk -F, 'BEGIN{rank=0} {rank++; printf "%-6d  %-8s  %-8s  %-10s  %-8s  %s\n", rank,$1,$2,$3,$4,$5}'
} || { echo "[err] could not parse CSV"; exit 3; }
