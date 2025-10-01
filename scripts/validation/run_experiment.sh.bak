#!/usr/bin/env bash
set -euo pipefail; set +H
IN_DIR="${IN_DIR:-validation/input}"; LIST="validation/work/dataset_rows.txt"; mkdir -p "$(dirname "$LIST")"; : > "$LIST"
i=0; for f in "$IN_DIR"/*.tsv; do [ -e "$f" ] || continue; i=$((i+1)); id=$(printf "face%03d" "$i"); rowfile=$(bash scripts/validation/face_to_ap_safe.sh "$f" "$id"); cat "$rowfile" >> "$LIST"; [ $i -ge 50 ] && break; done
[ $i -ge 50 ] || echo "WARNING: only $i faces found; proceeding."
OUTBIN="analysis/validation/SIGNED_DATASET.bin"; RECEIPT="analysis/validation/SIGNED_DATASET.receipt.tsv"
mkdir -p analysis/validation
bash scripts/validation/pack_dataset.sh "$LIST" "$OUTBIN" "$RECEIPT" >/dev/null
bash scripts/validation/sign_dataset.sh "$OUTBIN" "analysis/validation/corridor.receipt.tsv" >/dev/null
printf "%s\n" "dataset_bin	$OUTBIN" "receipt	$RECEIPT" >> "analysis/validation/corridor.receipt.tsv"
printf "%s\n" "DONE	$(date -u +%FT%TZ)" >> "analysis/validation/corridor.receipt.tsv"
echo "SIGNED_DATASET at $OUTBIN"
