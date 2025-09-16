#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/entropy"
j=$(ls -1 "$dir"/entv1-*.json 2>/dev/null | LC_ALL=C sort | tail -n 1)
[ -n "$j" ] || { echo "[err] $0: operation failed; check input and try again
sha="${j%.json}.sha256"; tfb=$(sed -n "s/^bytes: //p" .tau_ledger/timefolds/"$(ls -1 .tau_ledger/timefolds/tf-*.meta 2>/dev/null | LC_ALL=C sort | tail -1)" | head -n1 2>/dev/null || echo 0)
hc=$(tail -n 2 .tau_ledger/CHAIN 2>/dev/null | tr -d "\r" | awk "NR==1{a=\$0} NR==2{b=\$0} END{print (a==\"\"||b==\"\")?\"none\":(a==b?\"same\":\"changed\")}")
tmp="docs/.manifest.ent.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## entropy (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## entropy (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $(basename "${j%.json}")" >> "$tmp"
printf "%s\n" "head_change: $hc" >> "$tmp"
printf "%s\n" "timefold_bytes: $tfb" >> "$tmp"
printf "%s\n" "entropy_sha256: $(cat "$sha")" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
