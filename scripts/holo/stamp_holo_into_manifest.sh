#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/holo"
j=$(ls -1 "$dir"/holov1-.json 2>/dev/null | LC_ALL=C sort | tail -n 1)
[ -n "$j" ] || { echo "[err] no holo tensor found" >&2; exit 2; }
sha="${j%.json}.sha256"; [ -f "$sha" ] || { echo "[err] missing sha for $j" >&2; exit 2; }
hid=$(sed -n "s/."id":"\([^"]\)"./\1/p" "$j" | head -n 1)
utc=$(sed -n "s/."utc":"\([^"]\)"./\1/p" "$j" | head -n 1)
cl=$(sed -n "s/."chain_len":\([0-9]\)./\1/p" "$j" | head -n 1)
ol=$(sed -n "s/."oleans":\([0-9]\)./\1/p" "$j" | head -n 1)
bd=$(sed -n "s/."bytes_build":\([0-9]\)./\1/p" "$j" | head -n 1)
cdm=$(sed -n "s/."cache_density_per_mille":\([0-9]\)./\1/p" "$j" | head -n 1)
h=$(cat "$sha")
tmp="docs/.manifest.holo.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## holography (v1)") break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## holography (v1)" >> "$tmp"
printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $hid" >> "$tmp"
printf "%s\n" "utc: $utc" >> "$tmp"
printf "%s\n" "tensor_chain_len: $cl" >> "$tmp"
printf "%s\n" "tensor_oleans: $ol" >> "$tmp"
printf "%s\n" "tensor_bytes_build: $bd" >> "$tmp"
printf "%s\n" "tensor_cache_density_per_mille: $cdm" >> "$tmp"
printf "%s\n" "tensor_sha256: $(cat "$sha")" >> "$tmp"
printf "%s\n" "" >> "$tmp"
mv "$tmp" "$man"
