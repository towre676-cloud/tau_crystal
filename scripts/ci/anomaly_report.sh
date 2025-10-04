#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
out_tsv=${LEDGER_DIR}/BUDGET.report.tsv
out_txt=${LEDGER_DIR}/BUDGET.report.txt
sumfile=${LEDGER_DIR}/BUDGET.sum
advisory_sum=$( [ -f "$sumfile" ] && cat "$sumfile" || echo 0 )
tmp_vals=$(mktemp)
: > "$tmp_vals"
for f in "$LEDGER_DIR"/*_curvature.tsv; do
  [ -f "$f" ] || continue
  awk 'NF>=2{ s+=$2 } END{ print (s+0) }' "$f" >> "$tmp_vals"
done
if [ ! -s "$tmp_vals" ]; then
  echo "[report] no curvature TSVs in $LEDGER_DIR" >&2; : > "$out_tsv"; : > "$out_txt"; rm -f "$tmp_vals"; exit 0
fi
count=$(wc -l < "$tmp_vals" | awk "{print +\$1}")
agg=$(awk "{ s+=\$1 } END{ print (s+0) }" "$tmp_vals")
awk -v count="$count" -v agg="$agg" -v adv="$advisory_sum" 'BEGIN{print "key\tvalue"; print "files\t"count; print "aggregate_sum\t"agg; print "advisory_budget\t"adv}' > "$out_tsv"
echo "Anomaly Report"              >  "$out_txt"
echo "Files: $count"              >> "$out_txt"
echo "Aggregate: $agg"            >> "$out_txt"
echo "AdvisoryBudget: $advisory_sum" >> "$out_txt"
awk -v a="$agg" -v b="$advisory_sum" 'BEGIN{ if ((a-b)>1e-9 || (b-a)>1e-9) exit 1; else exit 0 }' || echo '[warn] advisory budget differs from aggregate by >1e-9' >&2
rm -f "$tmp_vals"
echo "[report] wrote $out_tsv and $out_txt" >&2
