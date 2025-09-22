#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/perma"
meta=$(ls -1 "$dir"/permav1-*.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$meta" ] || { echo "[err] no perma meta found; run pin_receipt_to_ipfs.sh"; exit 2; }
receipt=$(sed -n "s/^receipt: //p" "$meta" | head -n 1)
sha=$(sed -n "s/^sha256: //p" "$meta" | head -n 1)
cid=$(sed -n "s/^cid: //p" "$meta" | head -n 1)
[ -s ".tau_ledger/receipts/$receipt" ] || { echo "[FAIL] missing receipt: $receipt"; exit 1; }
have_sha=$(scripts/sha256.sh ".tau_ledger/receipts/$receipt")
[ "$have_sha" = "$sha" ] || { echo "[FAIL] receipt hash mismatch; want: $sha, have: $have_sha"; exit 1; }
[ "$cid" = "unpinned" ] && { echo "[OK] perma receipt verified: $receipt (unpinned)"; exit 0; }
have_cid=$(curl -s "https://ipfs.io/ipfs/$cid" | scripts/sha256.sh -)
[ "$have_cid" = "$sha" ] || { echo "[FAIL] IPFS CID content mismatch; want: $sha, have: $have_cid"; exit 1; }
echo "[OK] perma receipt verified: $receipt (CID: $cid)"
