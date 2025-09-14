#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/cache"
log=$(ls -1 "$dir"/cache-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$log" ] || { echo "[err] no cache log found"; exit 2; }
sha=$(scripts/meta/_sha256.sh "$log")
tmp="docs/.manifest.cache.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## cache (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## cache (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $(basename "${log%.json}")" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
