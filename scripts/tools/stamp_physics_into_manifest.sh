#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/physics"
json=$(ls -1 "$dir"/passport*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$json" ] || { echo "[err] no physics json found; check .tau_ledger/physics"; exit 2; }
id=$(jq -r .id "$json")
sha=$(scripts/sha256.sh "$json")
tmp="docs/.manifest.physics.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## physics (v1)"*) break ;; *) printf "%s\\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\\n" "## physics (v1)" >> "$tmp"; printf "%s\\n" "" >> "$tmp"
printf "%s\\n" "id: $id" >> "$tmp"
printf "%s\\n" "sha256: $sha" >> "$tmp"
printf "%s\\n" "" >> "$tmp"; mv "$tmp" "$man"
echo "[OK] stamped physics into manifest"
