#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
out="${LEDGER_DIR}/BUDGET_history.tsv"
: > "$out"
printf "ts\tcurvature_sum\n" >> "$out"
tmp="$(mktemp)"
for f in $(find "$LEDGER_DIR" -maxdepth 1 -type f -name "*_curvature.tsv" | sort); do
  base=$(basename "$f")
  ts=${base%%_*}
  sum=$(awk "NF>=2 {s+=\$2} END{printf \"%.12f\n\", (s+0)}" "$f")
  printf "%s\t%s\n" "$ts" "$sum" >> "$tmp"
done
if [ -s "$tmp" ]; then sort "$tmp" >> "$out"; fi
rm -f "$tmp"
echo "[collect] wrote $out"
exit 0
