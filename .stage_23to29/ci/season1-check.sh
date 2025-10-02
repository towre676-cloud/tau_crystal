#!/usr/bin/env bash
set -euo pipefail

echo "Checking file presence…"
for f in \
  docs/season1/cast.tsv \
  docs/season1/README.md \
  docs/season1/schema/season1.schema.json \
  kernel_contract.tsv
do
  [ -f "$f" ] || { echo "Missing file: $f" >&2; exit 1; }
done
echo "OK: required files present"

echo "Validating schema (bash+jq)…"
schema='docs/season1/schema/season1.schema.json'
grep -F '"$schema"' "$schema" >/dev/null || { echo 'Missing literal "$schema" key' >&2; exit 1; }
jq empty "$schema"
echo 'OK: schema parses and has literal "$schema"'

echo "TSV check (cast.tsv)…"
f="docs/season1/cast.tsv"
head -n1 "$f" | awk -F'\t' 'NF!=5{print "Bad header column count: " NF; exit 1}'
if [ "$(wc -l < "$f")" -gt 1 ]; then
  tail -n +2 "$f" | awk -F'\t' 'NF!=5{print "Bad row at file line " NR+1 " has " NF " columns"; exit 1}'
fi
echo "OK: cast.tsv columns are consistent (5)"

echo "TSV check (kernel_contract.tsv)…"
f="kernel_contract.tsv"
head -n1 "$f" | awk -F'\t' 'NF!=5{print "Bad header column count: " NF; exit 1}'
if [ "$(wc -l < "$f")" -gt 1 ]; then
  tail -n +2 "$f" | awk -F'\t' 'NF!=5{print "Bad row at file line " NR+1 " has " NF " columns"; exit 1}'
fi
echo "OK: kernel_contract.tsv columns are consistent (5)"

echo "Schema tail:"
tail -n 30 docs/season1/schema/season1.schema.json || true
echo "cast.tsv head:"
head -n 10 docs/season1/cast.tsv || true
echo "kernel_contract.tsv head:"
head -n 10 kernel_contract.tsv || true

# Optional finale budget check
if [ -f analysis/season1_finale.json ]; then
  rho=$(jq -r '.rho_R // empty' analysis/season1_finale.json)
  bud=$(jq -r '.pf_gap_budget_hint // empty' analysis/season1_finale.json)
  if [ -z "${rho:-}" ] || [ -z "${bud:-}" ]; then
    echo "finale missing rho_R/pf_gap_budget_hint" >&2; exit 1
  fi
  diff=$(awk -v r="$rho" -v b="$bud" 'BEGIN{printf "%.12f", (1.0 - r) - b}')
  awk -v d="$diff" 'BEGIN{exit (d<0?-d:d)<=1e-9 ? 0 : 1}' || { echo "budget mismatch: pf_gap_budget_hint != 1 - rho_R (Δ=$diff)"; exit 1; }
  echo "OK: finale budget equals 1 - rho_R"
fi

echo "All checks passed."
