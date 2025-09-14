#!/usr/bin/env bash
set -Eeuo pipefail; set +H
outdir=".tau_ledger/xref"; mkdir -p "$outdir"; : > "$outdir/index.v1"
for r in receipts/xref/*.json; do
  [ -s "$r" ] || continue
  sha=$(scripts/meta/_sha256.sh "$r")
  url=$(grep "url" "$r" | sed -E "s/.*: *\\"(.*)\\".*/\\1/" | head -n1)
  id=$(basename "$r" .json)
  echo "$id $sha $url" >> "$outdir/index.v1"
done
