#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; svg=".tau_ledger/interf/interference.svg"
[ -f "$svg" ] || { echo "[err] no svg interference file"; exit 2; }
sha=$(scripts/meta/_sha256.sh "$svg")
tmp="docs/.manifest.if.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## interference (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## interference (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "svg: $svg" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
