#!/usr/bin/env bash
set +H
set -euo pipefail
IFS=$(printf '\n\t')

REG_DIR=".tau_ledger/registry"
OUT=".tau_ledger/REGISTRY_ALL.tsv"
TMP_ALL="$(mktemp)"
TMP_FIX="$(mktemp)"
trap 'rm -f "$TMP_ALL" "$TMP_FIX"' EXIT

printf 'ts\ttype\tsha256\tmerkle_root\tsize_bytes\tsource\tpath\tgit_commit\tgit_status\n' > "$TMP_ALL"

[ -d "$REG_DIR" ] || { printf "No registry dir. Run receipt_index.sh and/or receipt_history.sh first.\n" >&2; exit 1; }

have=0
while IFS= read -r -d "" shard; do
  have=1
  awk "FNR>1{print}" "$shard" | tr -d "\r" >> "$TMP_ALL"
done < <(find "$REG_DIR" -maxdepth 1 -type f \( -name "index_*.tsv" -o -name "history_*.tsv" \) -print0)

[ "$have" -eq 1 ] || { printf "No registry shards found. Run receipt_index.sh and/or receipt_history.sh first.\n" >&2; exit 1; }

awk -F"\t" -v OFS="\t" 'NR==1{print;next} { if (NF==8 && $8 ~ /committed$/) { sub(/committed$/, "", $8); print $1,$2,$3,$4,$5,$6,$7,$8,"committed" } else if (NF>=9) { print $1,$2,$3,$4,$5,$6,$7,$8,$9 } else { for(i=NF+1;i<=9;i++) $i=""; print } }' "$TMP_ALL" > "$TMP_FIX"

awk -F"\t" -v OFS="\t" 'NR==1{hdr=$0; next} { k=$3 "|" $7 "|" $8; if(!(k in seen)){ seen[k]=1; rows[++n]=$0 } } END{ print hdr; for(i=1;i<=n;i++) print rows[i] }' "$TMP_FIX" > "$OUT"

total=$(awk "NR>1" "$OUT" | wc -l | awk "{print $1}")
uniq_paths=$(awk -F"\t" "NR>1{print $7}" "$OUT" | sort -u | wc -l | awk "{print $1}")
uniq_sha=$(awk -F"\t" "NR>1{print $3}" "$OUT" | sort -u | wc -l | awk "{print $1}")
uniq_merkle=$(awk -F"\t" "NR>1 && $4!=\"\"{print $4}" "$OUT" | sort -u | wc -l | awk "{print $1}")
missing_merkle=$(awk -F"\t" "NR>1 && $4==\"\"" "$OUT" | wc -l | awk "{print $1}")
deadbeef=$(awk -F"\t" "NR>1 && tolower($4)==\"deadbeef\"" "$OUT" | wc -l | awk "{print $1}")
printf "Wrote %s\n" "$OUT"
printf "rows=%s, unique_paths=%s, unique_sha256=%s, unique_merkle=%s, missing_merkle=%s, deadbeef=%s\n" "$total" "$uniq_paths" "$uniq_sha" "$uniq_merkle" "$missing_merkle" "$deadbeef"

