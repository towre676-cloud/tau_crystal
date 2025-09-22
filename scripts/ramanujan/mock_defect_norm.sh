#!/usr/bin/env bash
set -euo pipefail; set +H
GRID="${1:-ramanujan/data/mock_grid.tsv}"
[ -f "$GRID" ] || { echo "missing grid TSV: q<TAB>f(q)<TAB>shadow(q)"; exit 3; }
sum=0; n=0
while IFS=$'\t' read -r q f s; do
  [[ -z "${q:-}" ]] && continue
  if awk "BEGIN{exit (\"$f\"+0==\"$f\")?0:1}"; then
    if awk "BEGIN{exit (\"$s\"+0==\"$s\")?0:1}"; then
      diff=$(awk "BEGIN{printf(\"%.17g\", ($f + $s))}")
      sq=$(awk "BEGIN{printf(\"%.17g\", ($diff*$diff))}")
      sum=$(awk -v A="$sum" -v B="$sq" "BEGIN{printf(\"%.17g\", (A+B))}")
      n=$((n+1))
    fi
  fi
done < "$GRID"
[ "$n" -gt 0 ] || { echo "no numeric rows"; exit 4; }
norm=$(awk -v S="$sum" "BEGIN{printf(\"%.17g\", sqrt(S))}")
thr="${THRESHOLD:-1e-6}"
status="OK"; awk -v N="$norm" -v T="$thr" "BEGIN{exit (N<=T)?0:1}" || status="DEFECT_BOUND_EXCEEDED"
REC="ramanujan/receipts/mock_norm_$(date -u +%Y%m%dT%H%M%SZ).tsv"
printf "%s\n" "time\t$(date -u +%FT%TZ)" "rows\t$n" "norm\t$norm" "threshold\t$thr" "status\t$status" > "$REC"
echo "$REC"
