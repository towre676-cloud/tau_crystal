#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -eu; umask 022; export LC_ALL=C LANG=C

CSV="analysis/entropy/witness_scores.csv"
N="${1:-30}"
SORT_FIELD="${2:-cr_gz}"   # or H8_est, bits_per_byte_gz

[ -s "$CSV" ] || { echo "[err] missing: $CSV (run: witness_entropy_score.sh)"; exit 2; }

field_index() {
  awk -F, -v name="$1" '
    NR==1 { for(i=1;i<=NF;i++) if($i==name) print i; exit }
  ' "$CSV"
}

idx=$(field_index "$SORT_FIELD")
[ -n "$idx" ] || { echo "[err] sort field '$SORT_FIELD' not found in header"; exit 3; }

echo "Top $N by $SORT_FIELD (from $CSV)"
head -n 1 "$CSV"
tail -n +2 "$CSV" | LC_ALL=C sort -t, -k"$idx","$idx"nr | head -n "$N"
