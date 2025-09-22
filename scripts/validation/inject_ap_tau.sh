#!/usr/bin/env bash
set -euo pipefail; set +H
CSV="${1:-analysis/validation/ap_tau_by_face.csv}"
REC="${2:-analysis/validation/SIGNED_DATASET.receipt.tsv}"
[ -s "$CSV" ] || { echo "missing $CSV"; exit 1; }
[ -s "$REC" ] || { echo "missing $REC"; exit 1; }
MAP="$(mktemp)"; TMP="$(mktemp)"
header="$(head -n1 "$CSV")"; IFS=, read -r -a H <<<"$header"; [ "${#H[@]}" -ge 2 ] || { echo "bad header"; exit 1; }
tail -n +2 "$CSV" | while IFS=, read -r -a F; do
  [ "${#F[@]}" -ge 1 ] || continue; face="${F[0]}"; [ -n "$face" ] || continue; tokens="";
  for ((i=1;i<${#H[@]};i++)); do p="${H[$i]}"; v="${F[$i]:-}"; if [ -n "$v" ]; then tokens="$tokens ap_tau_p${p}:${v}"; fi; done
  printf "%s\t%s\n" "$face" "${tokens# }" >> "$MAP"
done
awk -F"\t" -vOFS="\t" -v MAP="$MAP" 'BEGIN{while((getline<MAP)>0){m[$1]=$2}}{k=$1; line=$0; gsub(/(^|[ \t])ap_tau_p[0-9]+:-?[0-9]+/,"",line); if(k in m && m[k]!=""){line=line"\t"m[k]} print line}' "$REC" > "$TMP"
mv "$TMP" "$REC"; rm -f "$MAP"
