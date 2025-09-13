#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; file=".tau_ledger/xref/index.v1"
[ -f "$file" ] || { echo "[err] missing $file"; exit 2; }
tmp="docs/.manifest.xref.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## federation (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## federation (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
while read -r id sha url; do
  printf "%s\n" "- id: $id" >> "$tmp"
  printf "%s\n" "  url: $url" >> "$tmp"
  printf "%s\n" "  sha256: $sha" >> "$tmp"
done < "$file"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
