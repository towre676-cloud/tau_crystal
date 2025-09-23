#!/usr/bin/env bash
set -e; set +H; umask 022
OUT_PRIV="hw/keys/device_p256.key"; OUT_PUB="hw/keys/device_p256.pub.pem"
openssl ecparam -name prime256v1 -genkey -noout -out "$OUT_PRIV"
openssl ec -in "$OUT_PRIV" -pubout -out "$OUT_PUB"
echo "[silicon] device keypair at $OUT_PRIV / $OUT_PUB"
