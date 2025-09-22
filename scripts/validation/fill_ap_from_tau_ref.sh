#!/usr/bin/env bash
set -euo pipefail; set +H
REF="${1:-analysis/validation/tau_reference.tsv}"
REC="${2:-analysis/validation/SIGNED_DATASET.receipt.tsv}"
OUT="${3:-analysis/validation/ap_tau_by_face.csv}"
[ -s "$REF" ] || { echo "missing $REF"; exit 1; }
[ -s "$REC" ] || { echo "missing $REC"; exit 1; }
PR="$(mktemp)"; MAP="$(mktemp)"; FACES="$(mktemp)"
awk -F"\t" "NR>1 && \$1+0>0{print \$1}" "$REF" | sort -n | awk '!seen[$0]++' > "$PR"
awk -F"\t" "NR>1{print \$1}" "$REC" | awk 'NF' | awk '!seen[$0]++' > "$FACES"
awk -F"\t" "NR>1 && \$1!=\"\"{print \$1\"\t\"\$3}" "$REF" > "$MAP"
printf "face" > "$OUT"; while read -r p; do printf ",%s" "$p" >> "$OUT"; done < "$PR"; printf "\n" >> "$OUT"
while read -r face; do [ -n "$face" ] || continue; printf "%s" "$face" >> "$OUT";
  while read -r p; do v=$(awk -F"\t" -v k="$p" '$1==k{print $2; exit}' "$MAP"); printf ",%s" "$v" >> "$OUT"; done < "$PR"; printf "\n" >> "$OUT";
done < "$FACES"
