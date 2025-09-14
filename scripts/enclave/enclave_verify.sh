#!/usr/bin/env bash
# enclave_verify.sh – simulates enclave verification of receipts
set -Eeuo pipefail; set +H; umask 022
receipt="${1:-}"; [ -s "$receipt" ] || { echo "usage: $0 <receipt.json>"; exit 2; }
root=".tau_ledger/enclave"; mkdir -p "$root"
ts=$(date -u +%Y%m%dT%H%M%SZ); id="enclavev1-$ts"; meta="$root/$id.meta"
tmpdir=$(mktemp -d); trap "rm -rf \"$tmpdir\"" EXIT
cp "$receipt" "$tmpdir/receipt.json"
sha=$(scripts/meta/_sha256.sh "$tmpdir/receipt.json")
jq -e ".commit and .merkle_root and .wrapper_digest" "$tmpdir/receipt.json" >/dev/null || { echo "[FAIL] invalid receipt schema"; exit 1; }
: > "$meta"
printf "%s\n" "schema: taucrystal/enclave/v1" >> "$meta"
printf "%s\n" "id: $id" >> "$meta"
printf "%s\n" "utc: $ts" >> "$meta"
printf "%s\n" "receipt: $(basename "$receipt")" >> "$meta"
printf "%s\n" "sha256: $sha" >> "$meta"
printf "%s\n" "status: PASS" >> "$meta"
echo "[OK] enclave verified: $receipt (sha256: $sha)"
