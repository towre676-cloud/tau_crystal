#!/usr/bin/env bash
set -euo pipefail; set +H
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
COEF_L="${1:-}"; COEF_R="${2:-}"; WEIGHT="${3:-}"; LEVEL="${4:-}"
if [ -z "$COEF_L" ] || [ -z "$COEF_R" ] || [ -z "$WEIGHT" ] || [ -z "$LEVEL" ]; then echo "usage: $0 left.tsv right.tsv weight level"; exit 2; fi
B="$("$ROOT/scripts/ramanujan/sturm_bound.sh" "$WEIGHT" "$LEVEL")"
[ -f "$COEF_L" ] && [ -f "$COEF_R" ] || { echo "missing coefficient files"; exit 3; }
head -n "$B" "$COEF_L" | awk -F"\t" "{print NR\"\t\" \$2}" > /tmp/L.$$
head -n "$B" "$COEF_R" | awk -F"\t" "{print NR\"\t\" \$2}" > /tmp/R.$$
if diff -u /tmp/L.$$ /tmp/R.$$ >/dev/null 2>&1; then status="OK"; msg="eta-identity verified to B='$B'"; else status="FAIL"; msg="mismatch within B='$B'"; fi
REC="$ROOT/ramanujan/receipts/eta_$(date -u +%Y%m%dT%H%M%SZ).tsv"
printf "%s\n" "time\t$(date -u +%FT%TZ)" "weight\t$WEIGHT" "level\t$LEVEL" "sturm\t$B" "status\t$status" > "$REC"
rm -f /tmp/L.$$ /tmp/R.$$
echo "$msg"; echo "$REC"
