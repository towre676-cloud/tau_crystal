#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
out_tsv=${LEDGER_DIR}/BUDGET.report.tsv
out_txt=${LEDGER_DIR}/BUDGET.report.txt
sumfile=${LEDGER_DIR}/BUDGET.sum
advisory_sum=$( [ -f "$sumfile" ] && cat "$sumfile" || echo 0 )
tmp_vals=$(mktemp); : > "$tmp_vals"
for f in "$LEDGER_DIR"/*_curvature.tsv; do [ -f "$f" ] || continue; awk "NF>=2{ s+=\$2 } END{ print (s+0) }" "$f" >> "$tmp_vals"; done
if [ ! -s "$tmp_vals" ]; then echo "[report] no curvature TSVs in $LEDGER_DIR" >&2; : > "$out_tsv"; : > "$out_txt"; rm -f "$tmp_vals"; exit 0; fi
count=$(wc -l < "$tmp_vals" | awk "{print +\$1}")
agg=$(awk "{ s+=\$1 } END{ print (s+0) }" "$tmp_vals")
mean=$(awk -v c="$count" "{ s+=\$1 } END{ if (c) print s/c; else print 0 }" "$tmp_vals")
std=$(awk -v c="$count" -v m="$mean" "{ d=(\$1-m); s+=d*d } END{ if (c) print sqrt(s/c); else print 0 }" "$tmp_vals")
maxabs=$(awk "function abs(x){return x<0?-x:x} { a=abs(\$1); if (a>mx) mx=a } END{ print (mx+0) }" "$tmp_vals")
qfile=$(mktemp); sort -g "$tmp_vals" > "$qfile"
q1_idx=$(( (count+3)/4 ))
q2_idx=$(( (count+1)/2 ))
q3_idx=$(( (3*count+1)/4 ))
q25=$(awk -v idx="$q1_idx" "NR==idx{print \$1}" "$qfile")
q50=$(awk -v idx="$q2_idx" "NR==idx{print \$1}" "$qfile")
q75=$(awk -v idx="$q3_idx" "NR==idx{print \$1}" "$qfile")
rm -f "$qfile"
awk -v files="$count" -v agg="$agg" -v adv="$advisory_sum" -v mean="$mean" -v std="$std" -v mx="$maxabs" -v q1="$q25" -v q2="$q50" -v q3="$q75" 'BEGIN{print "key\tvalue"; print "files\t"files; print "aggregate_sum\t"agg; print "advisory_budget\t"adv; print "mean\t"mean; print "std\t"std; print "max_abs\t"mx; print "q25\t"q1; print "q50\t"q2; print "q75\t"q3}' > "$out_tsv"
echo "Anomaly Report"                  >  "$out_txt"
echo "Files: $count"                  >> "$out_txt"
echo "Aggregate: $agg"                >> "$out_txt"
echo "AdvisoryBudget: $advisory_sum" >> "$out_txt"
echo "Mean: $mean"                    >> "$out_txt"
echo "Std: $std"                      >> "$out_txt"
echo "MaxAbs: $maxabs"                >> "$out_txt"
echo "Q25: $q25"                      >> "$out_txt"
echo "Q50: $q50"                      >> "$out_txt"
echo "Q75: $q75"                      >> "$out_txt"
awk -v a="$agg" -v b="$advisory_sum" 'BEGIN{ if ((a-b)>1e-9 || (b-a)>1e-9) exit 1; else exit 0 }' || echo '[warn] advisory budget differs from aggregate by >1e-9' >&2
rm -f "$tmp_vals"
echo "[report] wrote $out_tsv and $out_txt" >&2
