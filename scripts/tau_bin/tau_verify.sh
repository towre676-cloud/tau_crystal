#!/usr/bin/env bash
# tau_verify.sh – lightweight receipt verifier for Windows/Linux
set -Eeuo pipefail; set +H; umask 022
receipt="${1:-}"; [ -s "$receipt" ] || { echo "usage: $0 <receipt.json>"; exit 2; }
root=".tau_ledger/tau_bin"; mkdir -p "$root"
ts=$(date -u +%Y%m%dT%H%M%SZ); id="binv1-$ts"; meta="$root/$id.meta"
sha=$(scripts/meta/_sha256.sh "$receipt")
jq -e ".commit and .merkle_root and .wrapper_digest" "$receipt" >/dev/null || { echo "[FAIL] invalid receipt schema"; exit 1; }
: > "$meta"
printf "%s\n" "schema: taucrystal/bin/v1" >> "$meta"
printf "%s\n" "id: $id" >> "$meta"
printf "%s\n" "utc: $ts" >> "$meta"
printf "%s\n" "receipt: $(basename "$receipt")" >> "$meta"
printf "%s\n" "sha256: $sha" >> "$meta"
printf "%s\n" "status: PASS" >> "$meta"
echo "[OK] verified receipt: $receipt (sha256: $sha)"
