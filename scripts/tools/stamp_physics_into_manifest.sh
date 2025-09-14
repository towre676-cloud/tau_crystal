#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/physics"
j=$(ls -1 "$dir"/passport*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$j" ] || { echo "[err] no physics passport json"; exit 2; }
sha=$(scripts/meta/_sha256.sh "$j")
tmp="docs/.manifest.phys.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## physics (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## physics (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $(basename "${j%.json}")" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
