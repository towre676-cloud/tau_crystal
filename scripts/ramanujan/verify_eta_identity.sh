#!/usr/bin/env bash
set -euo pipefail; set +H
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
L="${1:-}"; R="${2:-}"; W="${3:-}"; N="${4:-}"
[ -n "${L:-}" ] && [ -n "${R:-}" ] && [ -n "${W:-}" ] && [ -n "${N:-}" ] || { echo "usage: $0 <left.tsv> <right.tsv> <weight> <level>"; exit 2; }
B="$("$ROOT/scripts/ramanujan/sturm_bound.sh" "$W" "$N")"
# strip optional header line beginning with # and keep first two columns
tail -n +1 "$L" | awk -F"\t" "NR==1 && /^#/ {next} {print \$1\"\t\"\$2}" | head -n "$B" > /tmp/L.$$
tail -n +1 "$R" | awk -F"\t" "NR==1 && /^#/ {next} {print \$1\"\t\"\$2}" | head -n "$B" > /tmp/R.$$
if diff -u /tmp/L.$$ /tmp/R.$$ >/dev/null 2>&1; then status="OK"; else status="FAIL"; fi
REC="$ROOT/ramanujan/receipts/eta_$(date -u +%Y%m%dT%H%M%SZ).tsv"
printf "%s\n" "time\t$(date -u +%FT%TZ)" "left\t$L" "right\t$R" "weight\t$W" "level\t$N" "sturm\t$B" "status\t$status" > "$REC"
rm -f /tmp/L.$$ /tmp/R.$$
echo "$status to B=$B"; echo "$REC"
[ "$status" = "OK" ]
