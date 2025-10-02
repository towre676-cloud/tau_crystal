#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; sec="$1"; shift || true
tmp="docs/.manifest.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## $sec (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## $sec (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
for kv in "$@"; do printf "%s\n" "$kv" >> "$tmp"; done
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
