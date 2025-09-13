#!/usr/bin/env bash
set -Eeuo pipefail; set +H
root=".tau_ledger/timefolds"; man="docs/manifest.md"
[ -d "$root" ] || { echo "[err] missing $root" >&2; exit 2; }
latest=$(ls -1 "$root"/tf-*.meta 2>/dev/null | LC_ALL=C sort | tail -n 1)
[ -n "$latest" ] || { echo "[err] no timefold meta found" >&2; exit 2; }
id=$(sed -n "s/^id: //p" "$latest" | head -n 1)
label=$(sed -n "s/^label: //p" "$latest" | head -n 1)
utc=$(sed -n "s/^utc: //p" "$latest" | head -n 1)
arc=$(sed -n "s/^archive: //p" "$latest" | head -n 1)
h=$(sed -n "s/^sha256: //p" "$latest" | head -n 1)
sz=$(sed -n "s/^bytes: //p" "$latest" | head -n 1)
cnt=$(sed -n "s/^files: //p" "$latest" | head -n 1)
tmp="docs/.manifest.tf.$$"; : > "$tmp"
[ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## timefold (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
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
