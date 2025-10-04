#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
N=${N:-3}
mkdir -p "$LEDGER_DIR"
br=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main)
sha=$(git rev-parse --short HEAD 2>/dev/null || echo 0000000)
ts=$(date -u +%Y%m%dT%H%M%SZ)
i=1
while [ "$i" -le "$N" ]; do
  t="${ts}_${br}_${sha}_r${i}_curvature.tsv"
  f="${LEDGER_DIR}/${t}"
  : > "$f"
  x=$(printf "0.000000000000" "$((100000000000*i))")
  printf "init	%s
" "$x" >> "$f"
  printf "close	-%s
" "$x" >> "$f"
  echo "[emit] $f"
  i=$((i+1))
done
