#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
outdir=".tau_ledger/xref"; mkdir -p "$outdir"; : > "$outdir/index.v1"
for r in receipts/xref/*.json; do
  [ -s "$r" ] || continue
  sha=$(scripts/meta/_sha256.sh "$r")
  url=$(awk -F\" '/\"url\"/{print $4; exit}' "$r" || true)
  id=$(basename "$r" .json)
  printf "%s\n" "$id $sha ${url:-none}" >> "$outdir/index.v1"
done
