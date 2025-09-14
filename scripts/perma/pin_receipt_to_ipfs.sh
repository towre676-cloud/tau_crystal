#!/usr/bin/env bash
# pin_receipt_to_ipfs.sh – pins a JSON receipt to IPFS and emits CID
set -Eeuo pipefail; set +H; umask 022
receipt="${1:-}"; [ -s "$receipt" ] || { echo "usage: $0 <receipt.json>"; exit 2; }
root=".tau_ledger/perma"; mkdir -p "$root"
ts=$(date -u +%Y%m%dT%H%M%SZ); id="permav1-$ts"; meta="$root/$id.meta"
sha=$(scripts/meta/_sha256.sh "$receipt")
if command -v ipfs >/dev/null 2>&1; then
  cid=$(ipfs add -Q "$receipt")
else
  cid=$(curl -s -F "file=@$receipt" https://ipfs.io/api/v0/add | jq -r .Hash)
  [ -n "$cid" ] || { echo "[err] failed to pin to IPFS"; exit 2; }
fi
: > "$meta"
printf "%s\n" "schema: taucrystal/perma/v1" >> "$meta"
printf "%s\n" "id: $id" >> "$meta"
printf "%s\n" "utc: $ts" >> "$meta"
printf "%s\n" "receipt: $(basename "$receipt")" >> "$meta"
printf "%s\n" "sha256: $sha" >> "$meta"
printf "%s\n" "cid: $cid" >> "$meta"
echo "[OK] pinned receipt: $receipt (CID: $cid)"
