#!/usr/bin/env bash
set -Eeuo pipefail; set +H
root=".tau_ledger/timefolds"; man="docs/manifest.md"
latest=$(ls -1 "$root"/tf-*.meta 2>/dev/null | LC_ALL=C sort | tail -1)
[ -n "$latest" ] || { echo "[err] no timefold meta found" >&2; exit 2; }
id=$(grep "^id:" "$latest" | awk "{print $2}")
label=$(grep "^label:" "$latest" | cut -d" " -f2- )
utc=$(grep "^utc:" "$latest" | awk "{print $2}")
arc=$(grep "^archive:" "$latest" | awk "{print $2}")
h=$(grep "^sha256:" "$latest" | awk "{print $2}")
sz=$(grep "^bytes:" "$latest" | awk "{print $2}")
cnt=$(grep "^files:" "$latest" | awk "{print $2}")
tmp="docs/.manifest.tf.$$"; : > "$tmp"
awk '{ if(index($0,"## timefold (v1)")==1) exit; print }' "$man" > "$tmp"
echo "## timefold (v1)" >> "$tmp"
echo "" >> "$tmp"
echo "id: $id" >> "$tmp"
echo "label: $label" >> "$tmp"
echo "utc: $utc" >> "$tmp"
echo "archive: $arc" >> "$tmp"
echo "sha256: $h" >> "$tmp"
echo "bytes: $sz" >> "$tmp"
echo "files: $cnt" >> "$tmp"
echo "" >> "$tmp"
mv "$tmp" "$man"
