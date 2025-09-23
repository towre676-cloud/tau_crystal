#!/usr/bin/env bash
set +H
umask 022
ROOT="analysis/validation"
REC="$ROOT/SIGNED_DATASET.receipt.tsv"
BIN="$ROOT/SIGNED_DATASET.bin"
OUT="$ROOT/run1_manifest.json"
COR="$ROOT/corridor.receipt.tsv"
mkdir -p "$ROOT"
if [ ! -f "$REC" ]; then echo "missing: $REC" >&2; exit 2; fi
DS_SHA=""; [ -f "$BIN" ] && DS_SHA=$(sha256sum "$BIN" 2>/dev/null | awk "{print \$1}")
RUN_TS=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf "{\\n" > "$OUT"
printf "  \\"type\\": \\"tau-crystal.face-run\\",\\n" >> "$OUT"
printf "  \\"version\\": \\"1.0\\",\\n" >> "$OUT"
printf "  \\"timestamp_utc\\": \\"%s\\",\\n" "$RUN_TS" >> "$OUT"
printf "  \\"dataset_bin_sha256\\": \\"%s\\",\\n" "$DS_SHA" >> "$OUT"
OPR=$(awk -F= '/^op_return_hex=/{print $2}' "$COR" 2>/dev/null | head -n1)
TXID=$(awk -F= '/^txid=/{print $2}' "$COR" 2>/dev/null | head -n1)
BLKH=$(awk -F= '/^block=/{print $2}' "$COR" 2>/dev/null | head -n1)
printf "  \\"chain_anchor\\": { \\"op_return_hex\\": \\"%s\\", \\"txid\\": \\"%s\\", \\"block\\": \\"%s\\" },\\n" "$OPR" "$TXID" "$BLKH" >> "$OUT"
printf "  \\"faces\\": [\\n" >> "$OUT"
i=0
while IFS=$'\t' read -r FACE_ID FACE_SHA META1 META2 META3; do
  [ -z "$FACE_ID" ] && continue
  SEP=","; [ $i -eq 0 ] && SEP=""
  printf "    %s{ \\"id\\": \\"%s\\", \\"sha256\\": \\"%s\\", \\"meta\\": [\\"%s\\", \\"%s\\", \\"%s\\"] }\\n" "$SEP" "$FACE_ID" "$FACE_SHA" "$META1" "$META2" "$META3" >> "$OUT"
  i=$((i+1))
done < <(awk "NR>1" "$REC")
printf "  ]\\n}\\n" >> "$OUT"
printf "wrote %s (%s faces)\\n" "$OUT" "$i"
