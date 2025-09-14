#!/usr/bin/env bash
# pin_receipt_to_ipfs.sh – pins a JSON receipt to IPFS and emits CID
set -Eeuo pipefail; set +H; umask 022
receipt="${1:-}"; [ -s "$receipt" ] || { echo "usage: $0 <receipt.json>"; exit 2; }
root=".tau_ledger/perma"; mkdir -p "$root"
ts=$(date -u +%Y%m%dT%H%M%SZ); id="permav1-$ts"; meta="$root/$id.meta"
sha=$(scripts/meta/_sha256.sh "$receipt")
cid="unpinned"
if command -v ipfs >/dev/null 2>&1; then
  cid=$(ipfs add -Q "$receipt" 2>/dev/null || echo "unpinned")
elif [ -n "${PINATA_API_KEY:-}" ] && [ -n "${PINATA_API_SECRET:-}" ]; then
  cid=$(curl -s -X POST -H "Authorization: Bearer $PINATA_API_KEY" -F "file=@$receipt" https://api.pinata.cloud/pinning/pinFileToIPFS | jq -r .IpfsHash 2>/dev/null || echo "unpinned")
else
  echo "[warn] no ipfs or Pinata API; CID set to unpinned"
fi
: > "$meta"
printf "%s\n" "schema: taucrystal/perma/v1" >> "$meta"
printf "%s\n" "id: $id" >> "$meta"
printf "%s\n" "utc: $ts" >> "$meta"
printf "%s\n" "receipt: $(basename "$receipt")" >> "$meta"
printf "%s\n" "sha256: $sha" >> "$meta"
printf "%s\n" "cid: $cid" >> "$meta"
echo "[OK] pinned receipt: $receipt (CID: $cid)"
