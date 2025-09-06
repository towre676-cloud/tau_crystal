# AUDIT — τ‑Crystal
## Verify MERKLE_ROOT matches repo state
git ls-files -z | xargs -0 sha256sum | LC_ALL=C sort -k2 > /tmp/list.txt
sha256sum /tmp/list.txt | awk '{print $1}'   # compare to docs/manifest.md

## Verify receipts and chain linkage
tail -n 5 .tau_ledger/CHAIN
sha256sum .tau_ledger/receipts/*.json | head

## Check receipt ↔ manifest root (jq optional)
jq -r '.merkle_root' tau-crystal-manifest.json
jq -r '.reflective.merkle_root' tau-crystal-receipt.json
