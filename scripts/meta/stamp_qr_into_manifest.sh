#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/qr"
svg=$(ls -1 "$dir"/qr-witness*.svg 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$svg" ] || { echo "[err] no QR SVG found"; exit 2; }
sha=$(scripts/meta/_sha256.sh "$svg")
tmp="docs/.manifest.qr.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## qr_witness (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## qr_witness (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: qr-witness-$(basename "${svg%.svg}")" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
