#!/usr/bin/env bash
set -Eeuo pipefail
seed="${1:-$RANDOM}"
out=".tau_ledger/motives/motive_${seed}.json"
mkdir -p "$(dirname "$out")"
# deterministic mint: SHA-256 of seed gives new τ-barcode
bar="$(echo -n "$seed" | openssl dgst -sha256 | awk '{print $2}')"
# split into 32-byte chunks → 32 τ-values ∈ [0,1]
awk -v b="$bar" 'BEGIN{
  split(b,hex,""); for(i=1;i<=64;i+=2){v=(("0x" hex[i] hex[i+1])+0)/255; printf "%.8f\n", v}
}' | jq -Rs '{seed:"'$seed'",tau:[splits("\n")]|map(select(length>0)|tonumber)}' > "$out"
echo "$out"
