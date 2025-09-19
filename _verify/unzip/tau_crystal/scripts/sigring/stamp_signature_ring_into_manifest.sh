#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/sigring"; j=$(ls -1 "$dir"/ringv1-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -n "$j" ] || { echo "[err] $0: operation failed; check input and try again
sha=$(scripts/meta/_sha256.sh "$j")
tmp="docs/.manifest.ring.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## signature_ring (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp";; esac; done < "$man"
printf "%s\n" "## signature_ring (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $(basename "${j%.json}")" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
