#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
tgt="${1:-}"
[ -n "$tgt" ] || { echo "usage: cache_attest.sh <file-or-dir>"; exit 2; }
[ -e "$tgt" ] || { echo "[cache] not found: $tgt"; exit 3; }
arch=$(uname -s)-$(uname -m)
commit=$(git rev-parse HEAD)
b3tmp=$(mktemp) ; : > "$b3tmp"
if [ -f "$tgt" ]; then
  blake3 "$tgt" | awk "{print \$1}" > "$b3tmp"
else
  find "$tgt" -type f -print0 | sort -z | xargs -0 blake3 | awk "{print \$1}" > "$b3tmp"
fi
key=$(awk '{printf "%s",$0}' "$b3tmp" | blake3 | awk "{print \$1}")
rm -f "$b3tmp"
man=".tau_ledger/cache/${key}.json"; : > "$man"
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
printf "%s" "{" >> "$man"
printf "%s" "\"commit\":\"$commit\",\"arch\":\"$arch\",\"target\":\"$tgt\",\"blake3\":\"$key\",\"utc\":\"$ts\"" >> "$man"
printf "%s\n" "}" >> "$man"
ln -sf "$man" ".tau_ledger/cache/latest.json"
echo "[cache] ok: $tgt → $key → $man"
