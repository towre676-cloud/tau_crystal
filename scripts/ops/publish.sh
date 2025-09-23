#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
ID="${1:?usage: publish.sh <capsule-id>}"
BASE="analysis/capsules/$ID"
TAR="$BASE/$ID.tar.gz"
SHAF="$TAR.sha256"
REC="$BASE/$ID.receipt.json"
PUBDIR="publish/$ID"
PUBKEY="seller_ed25519.pub.pem"
[ -f "$TAR" ] && [ -f "$SHAF" ] && [ -f "$REC" ] && [ -f "$PUBKEY" ] || { echo "missing anchor(s)"; exit 1; }
mkdir -p "$PUBDIR"
cp -f "$TAR" "$SHAF" "$REC" "$PUBKEY" "$PUBDIR"/
cp -f scripts/ops/acceptance_check_openssl.sh "$PUBDIR"/ 2>/dev/null || true
H=$(sha256sum "$TAR" | cut -d" " -f1); S=$(wc -c < "$TAR" | tr -d " ")
VF="$PUBDIR/VERIFY.txt"; : > "$VF"
printf "Verify %s (offline)\n\n" "$ID" >> "$VF"
printf "SHA-256: %s\nSize: %s bytes\n\n" "$H" "$S" >> "$VF"
cat >> "$VF" <<EOF
Files:
- auto-20250922T220241Z.tar.gz
- auto-20250922T220241Z.tar.gz.sha256
- auto-20250922T220241Z.receipt.json
- seller_ed25519.pub.pem

1) Check hash:
   sha256sum auto-20250922T220241Z.tar.gz | awk '{print $1}' | diff -u - auto-20250922T220241Z.tar.gz.sha256

2) Check receipt hash matches:
   grep -o '"sha256":"[^"]*' auto-20250922T220241Z.receipt.json | cut -d: -f3 | tr -d '"' \\
     | diff -u - auto-20250922T220241Z.tar.gz.sha256

3) Verify seller signature (OpenSSL/Ed25519):
   grep -o '"seller_sig":"ed25519_openssl:[^"]*' auto-20250922T220241Z.receipt.json \
     | sed 's/.*ed25519_openssl://' | tr -d '\r' | openssl base64 -d -A > sig.bin
   openssl pkeyutl -verify -pubin -inkey seller_ed25519.pub.pem -rawin \
     -sigfile sig.bin -in auto-20250922T220241Z.tar.gz && echo "Signature OK"
EOF
echo "[publish] wrote $PUBDIR and VERIFY.txt"; ls -l "$PUBDIR"
