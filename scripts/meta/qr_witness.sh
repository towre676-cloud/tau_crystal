#!/usr/bin/env bash
# qr_witness.sh – turns any JSON witness into a data-URI SVG QR code
set -Eeuo pipefail; set +H; umask 022
WITNESS="${1:-tau-crystal-manifest.json}"
OUT="${2:-.tau_ledger/witness_qr.svg}"
[ -s "$WITNESS" ] || { echo "[ERR] no witness"; exit 1; }
HASH=$(sha256sum "$WITNESS" | awk '{print $1}')
cat > "$OUT" <<EOF
<svg xmlns="http://www.w3.org/2000/svg" width="210" height="210">
  <rect width="100%%" height="100%%" fill="#ffffff"/>
  <text x="50%%" y="50%%" dominant-baseline="middle" text-anchor="middle" font-family="monospace" font-size="10">$HASH</text>
  <rect x="10" y="10" width="190" height="190" stroke="#000000" stroke-width="2" fill="none"/>
</svg>
EOF
jq --arg h "$HASH" --arg qr "$OUT" '. + {qr_witness: {hash: $h, svg_path: $qr}}' "$WITNESS" > tmp.json
mv tmp.json "$WITNESS"
echo "[OK] QR witness: $OUT  (hash: $HASH)"
