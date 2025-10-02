#!/usr/bin/env bash
set +H
umask 022
OUTDIR=".tau_ledger/discovery"; mkdir -p "$OUTDIR"
PKG="$OUTDIR/witness-run1-$(date -u +%Y%m%dT%H%M%SZ).tar.gz"
L="$OUTDIR/.witness_files.lst"; : > "$L"
for f in analysis/validation/SIGNED_DATASET.receipt.tsv analysis/validation/SIGNED_DATASET.bin analysis/validation/run1_manifest.json analysis/validation/face_tau_sequences.tsv analysis/validation/face_stats.tsv analysis/validation/corridor.receipt.tsv docs/monographs/ramanujan_face_run1.tex; do
  [ -f "$f" ] && printf "%s\n" "$f" >> "$L";
done
tar -czf "$PKG" -T "$L"
SHA=$(sha256sum "$PKG" | awk "{print \$1}")
COR="analysis/validation/corridor.receipt.tsv"; touch "$COR"
awk '{sub(/\r$/,""); print }' "$COR" > "$COR.tmp" && mv "$COR.tmp" "$COR"
sed -i "/^WITNESS_SHA=/d" "$COR" 2>/dev/null || true
printf "WITNESS_SHA=%s\n" "$SHA" >> "$COR"
echo "packed $PKG (sha256=$SHA) and stamped WITNESS_SHA"
