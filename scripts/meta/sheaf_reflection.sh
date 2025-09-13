#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
LEDGER=".tau_ledger"; CH="$LEDGER/CHAIN"; [ -f "$CH" ] || : > "$CH"
outdir="$LEDGER/sheaf"; mkdir -p "$outdir"
stamp=$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ); id="sheafv1-$stamp"; J="$outdir/$id.json"; S="$outdir/$id.sha256"
tmp="$outdir/.tmp.$$"; : > "$tmp"
prev=""; ladder=""; lines=0
while IFS= read -r h || [ -n "$h" ]; do
  [ -n "$h" ] || continue; echo "$prev $h" > "$tmp"; ladder=$(scripts/meta/_sha256.sh "$tmp"); prev="$ladder"; lines=$((lines+1))
done < "$CH"
bytes=$(wc -c < "$CH" | tr -d " ")
echo "{"                >  "$J"
printf "\"schema\":\"%s\",\n" "taucrystal/sheaf_reflection/v1" >> "$J"
printf "\"id\":\"%s\",\n" "$id"            >> "$J"
printf "\"utc\":\"%s\",\n" "$stamp"        >> "$J"
printf "\"chain_lines\":%s,\n" "$lines"    >> "$J"
printf "\"chain_bytes\":%s,\n" "$bytes"    >> "$J"
printf "\"ladder_hash\":\"%s\"\n" "$ladder">> "$J"
echo "}"               >> "$J"
scripts/meta/_sha256.sh "$J" > "$S"
man="docs/manifest.md"; tmpm="docs/.manifest.sheaf.$$"; : > "$tmpm"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## sheaf_reflection (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmpm" ;; esac; done < "$man"
printf "%s\n" "## sheaf_reflection (v1)" >> "$tmpm"
printf "%s\n" ""                         >> "$tmpm"
printf "%s\n" "id: $id"                  >> "$tmpm"
printf "%s\n" "ladder_sha256: $ladder"   >> "$tmpm"
printf "%s\n" "witness_sha256: $(cat "$S")" >> "$tmpm"
printf "%s\n" "chain_lines: $lines"      >> "$tmpm"
printf "%s\n" "chain_bytes: $bytes"      >> "$tmpm"
printf "%s\n" ""                         >> "$tmpm"
mv "$tmpm" "$man"
echo "OK: sheaf_reflection → $id ($ladder)"
