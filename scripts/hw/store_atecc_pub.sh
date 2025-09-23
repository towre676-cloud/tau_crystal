#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
PEM_IN="${1:?usage: store_atecc_pub.sh <pubkey.pem>}"; OUT="hw/keys/atecc_p256_pub.pem"
openssl ec -in "$PEM_IN" -pubin -noout >/dev/null 2>&1 || { echo "not a valid EC pubkey" >&2; exit 1; }
cp -f "$PEM_IN" "$OUT"; echo "[silicon] stored $OUT"
