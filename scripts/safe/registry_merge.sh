#!/usr/bin/env bash
set +H
set -euo pipefail
shopt -s nullglob
REG_DIR=".tau_ledger/registry"
OUT=".tau_ledger/REGISTRY_ALL.tsv"
TMP1="$OUT.tmp1"; TMP2="$OUT.tmp2"
mkdir -p ".tau_ledger"
: > "$TMP1"
printf "ts\ttype\tsha256\tmerkle_root\tsize_bytes\tsource\tpath\tgit_commit\tgit_status\n" >> "$TMP1"
for shard in "$REG_DIR"/index_*.tsv "$REG_DIR"/history_*.tsv; do
  [ -f "$shard" ] || continue
  tail -n +2 "$shard" | tr -d "\r" >> "$TMP1"
done
sed -E "s/([[:xdigit:]]{40})committed$/\1\tcommitted/" "$TMP1" > "$TMP2"
printf "ts\ttype\tsha256\tmerkle_root\tsize_bytes\tsource\tpath\tgit_commit\tgit_status\n" > "$OUT"
tail -n +2 "$TMP2" | sort -t $'\t' -k3,3 -k7,7 -k8,8 -u >> "$OUT"
rm -f "$TMP1" "$TMP2"
total=$(tail -n +2 "$OUT" | wc -l | awk "{print \$1}")
uniq_paths=$(tail -n +2 "$OUT" | cut -f7 | sort -u | wc -l | awk "{print \$1}")
uniq_sha=$(tail -n +2 "$OUT" | cut -f3 | sort -u | wc -l | awk "{print \$1}")
uniq_merkle=$(tail -n +2 "$OUT" | cut -f4 | grep -v "^[[:space:]]*$" | sort -u | wc -l | awk "{print \$1}")
missing_merkle=$(tail -n +2 "$OUT" | cut -f4 | grep -c "^[[:space:]]*$" || true)
printf "Wrote %s\n" "$OUT"
printf "rows=%s, unique_paths=%s, unique_sha256=%s, unique_merkle=%s, missing_merkle=%s\n" "$total" "$uniq_paths" "$uniq_sha" "$uniq_merkle" "$missing_merkle"
