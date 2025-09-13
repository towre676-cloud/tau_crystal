#!/usr/bin/env bash
set -Eeuo pipefail; set +H
file=".tau_ledger/xref/index.v1"; fail=0
[ -f "$file" ] || { echo "::error ::missing $file"; exit 1; }
while read -r id want url; do
  path="receipts/xref/$id.json"; [ -f "$path" ] || { echo "::error ::missing receipt $id"; fail=1; continue; }
  have=$(scripts/meta/_sha256.sh "$path")
  [ "$have" = "$want" ] || { echo "::error ::sha mismatch for $id"; fail=1; }
done < "$file"
[ "$fail" -eq 0 ] && echo "OK: all federation receipts verified" || { echo "FAIL: federation verification failed"; exit 1; }
