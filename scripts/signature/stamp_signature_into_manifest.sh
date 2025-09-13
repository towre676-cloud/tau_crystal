#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/signature"
sig=$(ls -1 "$dir"/sigv1-*.sig 2>/dev/null | LC_ALL=C sort | tail -n 1)
[ -n "$sig" ] || { echo "[err] no signature to stamp"; exit 2; }
sha="${sig%.sig}.sha256"; [ -f "$sha" ] || { echo "[err] missing sha for $sig"; exit 2; }
sid=$(basename "${sig%.sig}")
shex=$(cat "$sha")
tmp="docs/.manifest.sig.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## signature (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## signature (v1)" >> "$tmp"
printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $sid" >> "$tmp"
printf "%s\n" "signature_sha256: $shex" >> "$tmp"
printf "%s\n" "" >> "$tmp"
mv "$tmp" "$man"
