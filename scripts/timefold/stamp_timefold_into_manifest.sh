#!/usr/bin/env bash
set -Eeuo pipefail; set +H
root=".tau_ledger/timefolds"; man="docs/manifest.md"
latest=$(ls -1 "$root"/tf-.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -n "$latest" ] || { echo "[err] no timefold meta found" >&2; exit 2; }
id=$(grep "^id:" "$latest" | cut -d" " -f2-)
label=$(grep "^label:" "$latest" | cut -d" " -f2-)
utc=$(grep "^utc:" "$latest" | cut -d" " -f2-)
arc=$(grep "^archive:" "$latest" | cut -d" " -f2-)
h=$(grep "^sha256:" "$latest" | cut -d" " -f2-)
sz=$(grep "^bytes:" "$latest" | cut -d" " -f2-)
cnt=$(grep "^files:" "$latest" | cut -d" " -f2-)
tmp="docs/.manifest.tf.$$"; : > "$tmp"
if [ -f "$man" ]; then
 while IFS= read -r line; do
 case "$line" in
 "## timefold (v1)") break ;;
 *) printf "%s\n" "$line" >> "$tmp" ;;
 esac
 done < "$man"
fi
printf "%s\n" "## timefold (v1)" >> "$tmp"
printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $id" >> "$tmp"
printf "%s\n" "label: $label" >> "$tmp"
printf "%s\n" "utc: $utc" >> "$tmp"
printf "%s\n" "archive: $arc" >> "$tmp"
printf "%s\n" "sha256: $h" >> "$tmp"
printf "%s\n" "bytes: $sz" >> "$tmp"
printf "%s\n" "files: $cnt" >> "$tmp"
printf "%s\n" "" >> "$tmp"
mv "$tmp" "$man"
