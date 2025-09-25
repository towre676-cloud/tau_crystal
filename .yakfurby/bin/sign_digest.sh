#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
. ".yakfurby/bin/helpers.sh"; load_cfg
DGST="${1:?usage: sign_digest.sh <hex_sha256>}"; OUT="${2:?usage: ... <sig_out>}"; META="${3:-.yakfurby/tmp/sign.meta}"
mkdir -p .yakfurby/tmp; : > "$META"; printf "%s\n" "node_id=$NODE_ID" >> "$META"; printf "%s\n" "ts=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$META"
printf "%s" "$DGST" | xxd -r -p > .yakfurby/tmp/d.bin
if [ "${TPM_MODE}" = "auto" ] && have tpm2_sign && have tpm2_createprimary; then
  log "TPM sign attempt"; tpm2_createprimary -C o -g sha256 -G ecc -c .yakfurby/tmp/prim.ctx >/dev/null 2>&1 || true
  if [ -s .yakfurby/tmp/prim.ctx ]; then tpm2_create -G ecc -u .yakfurby/tmp/pub.pem -r .yakfurby/tmp/priv.pem -C .yakfurby/tmp/prim.ctx >/dev/null 2>&1 || true; fi
  if [ -s .yakfurby/tmp/pub.pem ] && [ -s .yakfurby/tmp/priv.pem ]; then tpm2_load -C .yakfurby/tmp/prim.ctx -u .yakfurby/tmp/pub.pem -r .yakfurby/tmp/priv.pem -c .yakfurby/tmp/key.ctx >/dev/null 2>&1 || true; fi
  if [ -s .yakfurby/tmp/key.ctx ]; then tpm2_sign -c .yakfurby/tmp/key.ctx -g sha256 -d .yakfurby/tmp/d.bin -f plain -o "$OUT" >/dev/null 2>&1 || true; fi
  if [ -s "$OUT" ]; then printf "%s\n" "provenance=tpm2" >> "$META"; exit 0; fi
  log "TPM path unavailable; falling back to software"
fi
SEC="$KEYS_DIR/ed25519.sec"; PUB="$KEYS_DIR/ed25519.pub"; mkdir -p "$KEYS_DIR"
if have ssh-keygen; then
  [ -f "$SEC" ] && [ -f "$PUB" ] || { ssh-keygen -t ed25519 -N "" -C "$NODE_ID" -f "$KEYS_DIR/ed25519" >/dev/null 2>&1 && mv "$KEYS_DIR/ed25519" "$SEC" && mv "$KEYS_DIR/ed25519.pub" "$PUB" && chmod 600 "$SEC"; }
  if ssh-keygen -Y sign -f "$SEC" -n file .yakfurby/tmp/d.bin > "$OUT" 2>/dev/null; then printf "%s\n" "provenance=ed25519_software_ssh" >> "$META"; exit 0; fi
fi
if have openssl; then
  [ -f "$SEC" ] && [ -f "$PUB" ] || {
    openssl genpkey -algorithm Ed25519 -out "$KEYS_DIR/ed25519.pem" >/dev/null 2>&1 || true
    [ -f "$KEYS_DIR/ed25519.pem" ] && openssl pkey -in "$KEYS_DIR/ed25519.pem" -pubout -out "$KEYS_DIR/ed25519.pub.pem" >/dev/null 2>&1 || true
    [ -f "$KEYS_DIR/ed25519.pem" ] || { log "OpenSSL keygen failed"; :; };
    [ -f "$KEYS_DIR/ed25519.pem" ] && { cp "$KEYS_DIR/ed25519.pem" "$SEC"; cp "$KEYS_DIR/ed25519.pub.pem" "$PUB"; chmod 600 "$SEC"; };
  }
  if [ -f "$SEC" ]; then openssl pkeyutl -sign -inkey "$SEC" -rawin -in .yakfurby/tmp/d.bin -out "$OUT" >/dev/null 2>&1 || true; fi
  if [ -s "$OUT" ]; then printf "%s\n" "provenance=ed25519_software_openssl" >> "$META"; exit 0; fi
fi
die "signing failed — no TPM, ssh-keygen, or openssl path succeeded"
