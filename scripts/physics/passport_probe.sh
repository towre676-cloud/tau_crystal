#!/usr/bin/env bash
set -Eeuo pipefail; set +H
OUT="${OUT:-analysis/passport_sig.tsv}"
mkdir -p "$(dirname "$OUT")"
tmpdir="$(mktemp -d)"; trap 'rm -rf "$tmpdir"' EXIT
sk="$tmpdir/sk.pem"; pub="$tmpdir/pub.pem"
b64dec(){ if command -v base64 >/dev/null 2>&1; then base64 -d; else openssl base64 -d; fi }
if [ -n "${PHYSICS_ED25519_SK_FILE:-}" ]; then cp -f "$PHYSICS_ED25519_SK_FILE" "$sk"
elif [ -n "${PHYSICS_ED25519_SK_B64:-}" ]; then printf "%s" "$PHYSICS_ED25519_SK_B64" | b64dec > "$sk"
else echo "[passport] missing PHYSICS_ED25519_SK_{FILE|B64}"; exit 5; fi
if [ -n "${PHYSICS_ED25519_PUB_FILE:-}" ]; then cp -f "$PHYSICS_ED25519_PUB_FILE" "$pub"
elif [ -n "${PHYSICS_ED25519_PUB_B64:-}" ]; then printf "%s" "$PHYSICS_ED25519_PUB_B64" | b64dec > "$pub"
else if ! openssl pkey -in "$sk" -pubout -out "$pub" >/dev/null 2>&1; then echo "[passport] cannot derive public key"; exit 5; fi; fi
nonce="$tmpdir/nonce.bin"; sig="$tmpdir/sig.bin"
head -c 32 /dev/urandom > "$nonce"
if ! openssl pkeyutl -sign -inkey "$sk" -rawin -in "$nonce" -out "$sig" >/dev/null 2>&1; then echo "[passport] sign failed"; exit 5; fi
if ! openssl pkeyutl -verify -pubin -inkey "$pub" -rawin -in "$nonce" -sigfile "$sig" >/dev/null 2>&1; then echo "[passport] verify failed"; pass=0; else pass=1; fi
tohex(){ od -An -tx1 -v -w1000 "$1" | tr -d " \n"; }
if ! openssl pkey -pubin -in "$pub" -outform DER -out "$tmpdir/pub.der" >/dev/null 2>&1; then
  if ! openssl pkey -in "$sk" -pubout -outform DER -out "$tmpdir/pub.der" >/dev/null 2>&1; then echo "[passport] cannot DER-encode pub"; exit 5; fi
fi
nonce_hex="$(tohex "$nonce")"
sig_hex="$(tohex "$sig")"
pub_hex="$(tohex "$tmpdir/pub.der")"
{ printf "nonce_hex\t%s\n" "$nonce_hex"; printf "sig_hex\t%s\n" "$sig_hex"; printf "pub_hex\t%s\n" "$pub_hex"; printf "pass\t%d\n" "$pass"; } > "$OUT"
echo "[passport] pass=$pass"
exit $([ "$pass" -eq 1 ] && echo 0 || echo 6)
