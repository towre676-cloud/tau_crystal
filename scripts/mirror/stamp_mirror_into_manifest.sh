#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/mirror"
meta=$(ls -1 "$dir"/mirrorv1-*.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$meta" ] || { echo "[err] no mirror meta found"; exit 2; }
id=$(sed -n "s/^id: //p" "$meta" | head -n 1)
remote=$(sed -n "s/^remote: //p" "$meta" | head -n 1)
sha=$(scripts/meta/_sha256.sh "$meta")
tmp="docs/.manifest.mirror.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## mirror (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## mirror (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $id" >> "$tmp"
printf "%s\n" "remote: $remote" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
