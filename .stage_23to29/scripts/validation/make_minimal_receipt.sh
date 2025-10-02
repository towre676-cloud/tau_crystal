#!/usr/bin/env bash
set +H
umask 022
IN="validation/input"
ROOT="analysis/validation"
REC="$ROOT/SIGNED_DATASET.receipt.tsv"
BIN="$ROOT/SIGNED_DATASET.bin"
mkdir -p "$ROOT"
: > "$REC"
printf "face_id\tsha256\tmeta1\tmeta2\tmeta3\n" >> "$REC"
: > "$BIN"
find "$IN" -maxdepth 1 -type f -name "*.tsv" | sort | while IFS= read -r F; do
  B=$(basename "$F")
  ID=${B%.*}
  S=$(sha256sum "$F" 2>/dev/null | awk "{print \$1}")
  [ -z "$S" ] && continue
  printf "%s\t%s\tap_tau:NA\tanchor:tsv\tlen:%s\n" "$ID" "$S" "$(wc -l < "$F" 2>/dev/null)" >> "$REC"
  printf "%s\n" "$S" >> "$BIN"
done
awk '{ sub(/\r$/,""); print }' "$REC" > "$REC.tmp" && mv "$REC.tmp" "$REC"
awk '{ sub(/\r$/,""); print }' "$BIN" > "$BIN.tmp" && mv "$BIN.tmp" "$BIN"
printf "wrote %s and %s\n" "$REC" "$BIN"
