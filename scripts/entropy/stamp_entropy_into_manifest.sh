#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/entropy"
j=$(ls -1 "$dir"/entv1-*.json 2>/dev/null | LC_ALL=C sort | tail -n 1)
[ -n "$j" ] || { echo "[err] no entropy witness found" >&2; exit 2; }
sha="${j%.json}.sha256"; [ -f "$sha" ] || { echo "[err] missing sha for $j" >&2; exit 2; }
eid=$(sed -n "s/.*\"id\":\"\\([^\"]*\\)\".*/\\1/p" "$j" | head -n 1)
utc=$(sed -n "s/.*\"utc\":\"\\([^\"]*\\)\".*/\\1/p" "$j" | head -n 1)
cl=$(sed -n "s/.*\"lines\":\\([0-9]*\\).*/\\1/p" "$j" | head -n 1)
cb=$(sed -n "s/.*\"bytes\":\\([0-9]*\\).*/\\1/p" "$j" | head -n 1)
gr=$(sed -n "s/.*\"gzip_ratio_per_mille\":\\([0-9]*\\).*/\\1/p" "$j" | head -n 1)
hc=$(sed -n "s/.*\"head_change\":\"\\([^\"]*\\)\".*/\\1/p" "$j" | head -n 1)
tfb=$(sed -n "s/.*\"timefolds\":{[^}]*\"bytes\":\\([0-9]*\\).*/\\1/p" "$j" | head -n 1)
tmp="docs/.manifest.ent.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## entropy (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## entropy (v1)" >> "$tmp"
printf "%s\n" "" >> "$tmp"
printf "%s\n" "id: $eid" >> "$tmp"
printf "%s\n" "utc: $utc" >> "$tmp"
printf "%s\n" "chain_lines: $cl" >> "$tmp"
printf "%s\n" "chain_bytes: $cb" >> "$tmp"
printf "%s\n
" "gzip_ratio_per_mille: '$gr' "
" >> "$tmp"
printf "%s\n" "head_change: $hc" >> "$tmp"
printf "%s\n" "timefold_bytes: $tfb" >> "$tmp"
printf "%s\n" "entropy_sha256: $(cat "$sha")" >> "$tmp"
printf "%s\n" "" >> "$tmp"
mv "$tmp" "$man"
