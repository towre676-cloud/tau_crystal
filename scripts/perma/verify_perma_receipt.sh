#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/perma"
meta=$(ls -1 "$dir"/permav1-*.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$meta" ] || { echo "[err] no perma meta found"; exit 2; }
receipt=$(sed -n "s/^receipt: //p" "$meta" | head -n 1)
sha=$(sed -n "s/^sha256: //p" "$meta" | head -n 1)
cid=$(sed -n "s/^cid: //p" "$meta" | head -n 1)
[ -s ".tau_ledger/receipts/$receipt" ] || { echo "[FAIL] missing receipt: $receipt"; exit 1; }
have_sha=$(scripts/meta/_sha256.sh ".tau_ledger/receipts/$receipt")
[ "$have_sha" = "$sha" ] || { echo "[FAIL] receipt hash mismatch"; echo "want: $sha"; echo "have: $have_sha"; exit 1; }
have_cid=$(curl -s "https://ipfs.io/ipfs/$cid" | sha256sum | awk "{print \$1}")
[ "$have_cid" = "$sha" ] || { echo "[FAIL] IPFS CID content mismatch"; echo "want: $sha"; echo "have: $have_cid"; exit 1; }
echo "[OK] perma receipt verified: $receipt (CID: $cid)"
