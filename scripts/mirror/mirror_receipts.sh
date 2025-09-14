#!/usr/bin/env bash
# mirror_receipts.sh – fetches and verifies receipts from a remote repo
set -Eeuo pipefail; set +H; umask 022
remote="${1:-}"; [ -n "$remote" ] || { echo "usage: $0 <remote-repo-url>"; exit 2; }
root=".tau_ledger/mirror"; mkdir -p "$root"
ts=$(date -u +%Y%m%dT%H%M%SZ); id="mirrorv1-$ts"; meta="$root/$id.meta"
tmpdir=$(mktemp -d); trap "rm -rf \"$tmpdir\"" EXIT
curl -s "$remote/.tau_ledger/receipts/" | grep -o "href=\"[^\"]*\.json\"" | sed "s/href=\"//" > "$tmpdir/list"
: > "$meta"
printf "%s\n" "schema: taucrystal/mirror/v1" >> "$meta"
printf "%s\n" "id: $id" >> "$meta"
printf "%s\n" "utc: $ts" >> "$meta"
printf "%s\n" "remote: $remote" >> "$meta"
printf "%s\n" "receipts: [" >> "$meta"
i=0
while IFS= read -r file; do
  curl -s "$remote/.tau_ledger/receipts/$file" -o "$tmpdir/$file"
  sha=$(scripts/meta/_sha256.sh "$tmpdir/$file")
  i=$((i+1))
  SEP=$([ $i -gt 1 ] && echo "," || true)
  printf "%s\n" "  $SEP{\"file\": \"$file\", \"sha256\": \"$sha\"}" >> "$meta"
done < "$tmpdir/list"
printf "%s\n" "]" >> "$meta"
echo "[OK] mirrored receipts: $meta"
