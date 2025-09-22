#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
export LC_ALL=C LANG=C
IDX="${1:-corridor/capsules/index.tsv}"
SIG="${2:-.tau_ledger/capsules/index.sha256}"
TMP=".tau_ledger/capsules/.wtmp"; mkdir -p "$(dirname "$SIG")" "$TMP"
if [ ! -f "$IDX" ]; then printf "%s\n" "capsule\tpath\tmerkle\twhen_utc\tprovenance" > "$IDX"; fi
head -n 1 "$IDX" | tr -d "\r" > "$TMP/.norm.tsv"
if [ -s "$IDX" ]; then
  tail -n +2 "$IDX" 2>/dev/null | tr -d "\r" | awk 'BEGIN{OFS="\t"} {sub(/[ \t]+$/,"",$0); if(NF>0) print $0}' | LC_ALL=C sort -u >> "$TMP/.norm.tsv"
fi
cp -f "$TMP/.norm.tsv" "$IDX"
sha256sum "$IDX" | awk "{print \$1}" > "$SIG"
printf "[CAPSULES] wrote %s and %s\n" "$IDX" "$SIG"
