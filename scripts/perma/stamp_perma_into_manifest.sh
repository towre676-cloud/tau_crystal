#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/perma"
meta=$(ls -1 "$dir"/permav1-*.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$meta" ] || { echo "[err] no perma meta found"; exit 2; }
id=$(sed -n "s/^id: //p" "$meta" | head -n 1)
receipt=$(sed -n "s/^receipt: //p" "$meta" | head -n 1)
sha=$(sed -n "s/^sha256: //p" "$meta" | head -n 1)
cid=$(sed -n "s/^cid: //p" "$meta" | head -n 1)
tmp="docs/.manifest.perma.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## perma_receipt (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## perma_receipt (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $id" >> "$tmp"
printf "%s\n" "receipt: $receipt" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "cid: $cid" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
