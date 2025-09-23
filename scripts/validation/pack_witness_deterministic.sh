#!/usr/bin/env bash
set -euo pipefail; set +H
OUTDIR=".tau_ledger/discovery"; mkdir -p "$OUTDIR"
TS="1970-01-01"
NAME="witness-$(date -u +%Y%m%dT%H%M%SZ).tar.gz"
tar --sort=name --mtime="$TS" --owner=0 --group=0 --numeric-owner -c -f - \
  analysis/validation/SIGNED_DATASET.bin \
  analysis/validation/SIGNED_DATASET.receipt.tsv \
  analysis/validation/corridor.receipt.tsv \
  analysis/validation/run1_manifest.json \
  2>/dev/null | gzip -n > "$OUTDIR/$NAME"
sha256sum "$OUTDIR/$NAME" | awk "{print \$1}"
