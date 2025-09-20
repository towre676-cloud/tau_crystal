#!/usr/bin/env bash
set -euo pipefail
IDX="analysis/geom/canonical_companions.tsv"
[ -f "$IDX" ] || { echo "::error::missing $IDX"; exit 1; }
# read index (skip header)
tail -n +2 "$IDX" | while IFS=$'\t' read -r typ path hash; do
  [ -f "$path" ] || { echo "::error::missing companion $typ at $path"; exit 1; }
  cur=$(sha256sum "$path" | awk '{print $1}')
  if [ "$cur" != "$hash" ]; then
    echo "::error::hash mismatch for $typ: index=$hash current=$cur"
    echo "Update index via: make sure to re-run companion indexing step (commit with RECANONIZE=TRUE if intentional)."
    exit 1
  fi
done
echo "Companion guard OK."
