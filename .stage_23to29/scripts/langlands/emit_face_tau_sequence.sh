#!/usr/bin/env bash
set +H
umask 022
REC="analysis/validation/SIGNED_DATASET.receipt.tsv"
OUT="analysis/validation/face_tau_sequences.tsv"
if [ ! -f "$REC" ]; then echo "missing: $REC" >&2; exit 2; fi
: > "$OUT"
printf "face_id\tsha256\tap_tau_sequence\n" >> "$OUT"
awk "NR>1" "$REC" | while IFS=$'\t' read -r FID FSH A1 A2 A3; do
  # harvest any embedded ap_tau fields if present in receipt metadata; else produce NA placeholders
  SEQ=$(printf "%s" "$A1 $A2 $A3" | awk '{for(i=1;i<=NF;i++){if($i ~ /^ap_tau:/){gsub(/^ap_tau:/,"",$i); printf("%s%s",$i,(i<NF?",":""))}}}')
  [ -z "$SEQ" ] && SEQ="NA,NA,NA"
  printf "%s\t%s\t%s\n" "$FID" "$FSH" "$SEQ" >> "$OUT"
done
printf "wrote %s\n" "$OUT"
