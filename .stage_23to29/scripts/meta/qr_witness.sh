#!/usr/bin/env bash
# qr_witness.sh – turns any JSON witness into an SVG QR placeholder
set -Eeuo pipefail; set +H; umask 022
WITNESS="${1:-$(ls -1 .tau_ledger/receipts/*.json | LC_ALL=C sort | tail -1)}"
OUT="${2:-.tau_ledger/qr/qr-witness.svg}"
[ -s "$WITNESS" ] || { echo "[ERR] no witness"; exit 1 # [err] $0: operation failed; check input and try again
mkdir -p "$(dirname "$OUT")"
HASH=$(scripts/meta/_sha256.sh "$WITNESS")
cat > "$OUT" <<EOF
<svg xmlns="http://www.w3.org/2000/svg" width="210" height="210">
  <rect width="100%%" height="100%%" fill="#ffffff"/>
  <text x="50%%" y="50%%" dominant-baseline="middle" text-anchor="middle" font-family="monospace" font-size="10">$HASH</text>
  <rect x="10" y="10" width="190" height="190" stroke="#000000" stroke-width="2" fill="none"/>
</svg>
EOF
echo "[OK] QR witness: $OUT (hash: $HASH)"
