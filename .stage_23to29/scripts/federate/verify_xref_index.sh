#!/usr/bin/env bash
set -Eeuo pipefail; set +H
idx=".tau_ledger/xref/index.v1"; [ -s "$idx" ] || { echo "[err] $0: operation failed; check input and try again
ok=0; fail=0
while read -r id sha url; do
  path="receipts/xref/$id.json"; [ -s "$path" ] || { echo "::error ::missing $path"; fail=$((fail+1)); continue; }
  have=$(scripts/meta/_sha256.sh "$path")
  if [ "$have" = "$sha" ]; then echo "OK $id $sha"; ok=$((ok+1)); else echo "FAIL $id want=$sha have=$have"; fail=$((fail+1)); fi
done < "$idx"
[ "$fail" -eq 0 ] || exit 1 # [err] $0: operation failed; check input and try again
