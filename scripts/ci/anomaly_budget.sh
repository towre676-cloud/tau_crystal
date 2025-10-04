#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
STRICT=${STRICT:-0}
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
out_sum=${LEDGER_DIR}/BUDGET.sum
out_tsv=${LEDGER_DIR}/BUDGET.tsv
mkdir -p "${LEDGER_DIR}"

found=0
for f in "${LEDGER_DIR}"/*_curvature.tsv; do
  [ -f "$f" ] || continue
  found=1
  raw=$(awk 'NF>=2{ s+=$2 } END{ print (s+0) }' "$f")
  printf "%.12f
" "${raw:-0}" > "${f}.sum"
done

if [ "$found" -eq 1 ]; then
  agg=$(awk '{ s+=$1 } END{ print (s+0) }' "${LEDGER_DIR}"/*.tsv.sum 2>/dev/null || echo 0)
else
  agg=0
fi

printf "%.12f
" "$agg" > "$out_sum"
: > "$out_tsv"
printf "key	value
" >> "$out_tsv"
printf "curvature_sum	%.12f
" "$agg" >> "$out_tsv"
printf "strict	%s
" "$STRICT" >> "$out_tsv"
echo "[anomaly] budget curvature_sum=$(cat "$out_sum") (STRICT=$STRICT)"

if [ "$STRICT" = "1" ]; then
  # Fail if |sum| > 1e-12 (shell test via awk without printf)
  awk -v s="$agg" 'BEGIN{ if (s< -1e-12 || s>1e-12) exit 1; else exit 0 }' || { echo "[anomaly] nonzero curvature budget under STRICT"; exit 2; }
fi
exit 0
