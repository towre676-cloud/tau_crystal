#!/usr/bin/env bash
set -euo pipefail
WIT="${1:-.tau_ledger/lean_proof_v2.json}"
[ -f "$WIT" ] || { echo "::error::missing $WIT"; exit 1; }

_hash() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then openssl dgst -sha256 "$1" | awk '{print $NF}'
  else echo ""; fi
}

SHA="$(_hash "$WIT")"
[ -n "$SHA" ] || { echo "::error::no sha256 tool available"; exit 1; }
TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
BAS="$(basename "$WIT")"

# Update corridor receipt
touch corridor.receipt.tsv
printf "%s\t%s\t%s\t%s\n" "$TS" "$BAS" "$SHA" "coho:lean_witness" >> corridor.receipt.tsv

# Update CHAIN (file or dir)
if [ -d ".tau_ledger/CHAIN" ]; then
  CHAINF=".tau_ledger/CHAIN/COHO.chain.tsv"
else
  CHAINF=".tau_ledger/CHAIN"
fi
mkdir -p "$(dirname "$CHAINF")"
touch "$CHAINF"
printf "%s\t%s\t%s\t%s\n" "$TS" "$BAS" "$SHA" "coho:lean_witness" >> "$CHAINF"

# Expose for later CI step
echo "WITNESS_SHA=$SHA" >> "$GITHUB_ENV" 2>/dev/null || true
echo "::notice::stamped $BAS (sha256=$SHA)"
