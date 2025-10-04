#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
N=${N:-3}
mkdir -p "$LEDGER_DIR"
i=1
while [ "$i" -le "$N" ]; do
  f="$LEDGER_DIR/sample_r${i}_curvature.tsv"
  : > "$f"
  printf "init	1.000000000000e-12
" >> "$f"
  printf "close	-1.000000000000e-12
" >> "$f"
  echo "[emit] $f"
  i=$((i+1))
done
