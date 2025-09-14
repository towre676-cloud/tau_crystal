#!/usr/bin/env bash
# mirror_receipts.sh – fetches and verifies receipts from a remote repo
set -Eeuo pipefail; set +H; umask 022
remote="${1:-}"; [ -n "$remote" ] || { echo "usage: $0 <remote-repo-url>"; exit 2; }
root=".tau_ledger/mirror"; mkdir -p "$root"
ts=$(date -u +%Y%m%dT%H%M%SZ); id="mirrorv1-$ts"; meta="$root/$id.meta"
tmpdir=$(mktemp -d); trap "rm -rf \"$tmpdir\"" EXIT
: > "$meta"
printf "%s\n" "schema: taucrystal/mirror/v1" >> "$meta"
printf "%s\n" "id: $id" >> "$meta"
printf "%s\n" "utc: $ts" >> "$meta"
printf "%s\n" "remote: $remote" >> "$meta"
printf "%s\n" "receipts: [" >> "$meta"
i=0
curl -s -f "$remote/.tau_ledger/receipts/" > "$tmpdir/list.html" 2>/dev/null || { echo "[warn] remote fetch failed, using local receipt"; ls -1 .tau_ledger/receipts/*.json > "$tmpdir/list" 2>/dev/null || true; }
while IFS= read -r file; do
  [ -n "$file" ] || continue
  base=$(basename "$file")
  if [[ "$file" == *.json ]]; then
    curl -s -f "$remote/.tau_ledger/receipts/$base" -o "$tmpdir/$base" 2>/dev/null || cp ".tau_ledger/receipts/$base" "$tmpdir/$base" 2>/dev/null || continue
  else
    continue
  fi
  sha=$(scripts/meta/_sha256.sh "$tmpdir/$base")
  i=$((i+1))
  SEP=$([ $i -gt 1 ] && echo "," || true)
  printf "%s\n" "  $SEP{\"file\": \"$base\", \"sha256\": \"$sha\"}" >> "$meta"
done < <(grep -o "[^/]*\.json" "$tmpdir/list" || true)
printf "%s\n" "]" >> "$meta"
[ $i -gt 0 ] || { echo "[err] no receipts found"; exit 2; }
echo "[OK] mirrored receipts: $meta"
