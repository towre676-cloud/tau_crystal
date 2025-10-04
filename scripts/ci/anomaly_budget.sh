#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
STRICT=${STRICT:-0}
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
out_sum="${LEDGER_DIR}/BUDGET.sum"
out_tsv="${LEDGER_DIR}/BUDGET.tsv"
mkdir -p "${LEDGER_DIR}"

# Scan for "*_curvature.tsv", write a per-file .sum, then sum them into BUDGET.{sum,tsv}.
total=0
found=0
OIFS=$IFS; IFS='\n'
for f in $(find "${LEDGER_DIR}" -maxdepth 1 -type f -name "*_curvature.tsv" | sort); do
  [ -f "$f" ] || continue
  found=1
  awk "NF>=2 {s+=\$2} END{printf \"%.12f\n\", (s+0)}" "$f" > "${f}.sum"
done
IFS=$OIFS

if [ "$found" -eq 1 ]; then
  OIFS=$IFS; IFS='\n'
  for s in $(find "${LEDGER_DIR}" -maxdepth 1 -type f -name "*_curvature.tsv.sum" | sort); do
    v=$(awk "{print \$1+0}" "$s" 2>/dev/null || echo 0)
    total=$(awk -v a="$total" -v b="$v" "BEGIN{printf \"%.12f\n\", a+b}")
  done
  IFS=$OIFS
else
  total=0
fi

printf "%.12f\n" "$total" > "$out_sum"
: > "$out_tsv"
printf "key\tvalue\n" >> "$out_tsv"
printf "curvature_sum\t%.12f\n" "$total" >> "$out_tsv"
printf "strict\t%s\n" "$STRICT" >> "$out_tsv"
echo "[anomaly] budget curvature_sum=$total (STRICT=$STRICT)"
if [ "$STRICT" = "1" ]; then
  awk -v s="$total" "BEGIN{ if (s < -1e-12 || s > 1e-12) exit 1; else exit 0 }" || { echo "[anomaly] nonzero curvature budget under STRICT"; exit 2; }
fi
exit 0
