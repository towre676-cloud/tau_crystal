#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
out_tsv=${LEDGER_DIR}/BUDGET.report.tsv
out_txt=${LEDGER_DIR}/BUDGET.report.txt
sumfile=${LEDGER_DIR}/BUDGET.sum
advisory_sum=$( [ -f "$sumfile" ] && cat "$sumfile" || echo 0 )
tmp_vals=$(mktemp)
: > "$tmp_vals"
for f in "${LEDGER_DIR}"/*_curvature.tsv; do
  [ -f "$f" ] || continue
  raw=$(awk 'NF>=2{ s+=$2 } END{ print (s+0) }' "$f")
  printf "%s
" "${raw:-0}" >> "$tmp_vals"
done
if [ ! -s "$tmp_vals" ]; then
  echo "[report] no curvature TSVs in $LEDGER_DIR" >&2; : > "$out_tsv"; : > "$out_txt"; rm -f "$tmp_vals"; exit 0
fi
count=$(wc -l < "$tmp_vals" | awk '{print +$1}')
agg_raw=$(awk '{ s+=$1 } END{ print (s+0) }' "$tmp_vals")
mean_raw=$(awk -v c="$count" '{ s+=$1 } END{ if (c) print s/c; else print 0 }' "$tmp_vals")
std_raw=$(awk -v c="$count" -v m="$mean_raw" '{ d=($1-m); s+=d*d } END{ if (c) print sqrt(s/c); else print 0 }' "$tmp_vals")
maxabs_raw=$(awk 'function abs(x){return x<0?-x:x} { a=abs($1); if (a>mx) mx=a } END{ print (mx+0) }' "$tmp_vals")
printf "key	value
" > "$out_tsv"
printf "files	%s
" "$count" >> "$out_tsv"
printf "aggregate_sum	%.12f
" "$agg_raw" >> "$out_tsv"
printf "advisory_budget	%.12f
" "$advisory_sum" >> "$out_tsv"
printf "mean	%.12f
std	%.12f
max_abs	%.12f
" \n  "$mean_raw" "$std_raw" "$maxabs_raw" >> "$out_tsv"
printf "Anomaly Report
Files: %s
Aggregate: %.12f
AdvisoryBudget: %.12f
Mean: %.12f
Std: %.12f
MaxAbs: %.12f
" \n  "$count" "$agg_raw" "$advisory_sum" "$mean_raw" "$std_raw" "$maxabs_raw" > "$out_txt"
awk -v a="$agg_raw" -v b="$advisory_sum" 'BEGIN{ if ((a-b)>1e-9 || (b-a)>1e-9) exit 1; else exit 0 }' || \n  echo "[warn] advisory budget differs from aggregate by >1e-9" >&2
rm -f "$tmp_vals"
echo "[report] wrote $out_tsv and $out_txt" >&2
