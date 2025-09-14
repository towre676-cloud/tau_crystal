#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/evolver"
json=$(ls -1 "$dir"/evolver-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$json" ] || { echo "[err] no evolver json found"; exit 2; }
sha=$(scripts/meta/_sha256.sh "$json")
tmp="docs/.manifest.evolver.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## evolver (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## evolver (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $(basename "${json%.json}")" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
