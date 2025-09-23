#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
TAR="${1:?usage: acceptance_check_openssl.sh <tar.gz> <sha256-file> <receipt.json> <seller_pub_pem>}"
SHA_FILE="${2:?}"; REC="${3:?}"; PUB="${4:?}"
die(){ echo "[accept] ERROR: $*" >&2; exit 1; }
[ -f "$TAR" ] || die "missing TAR: $TAR"
[ -f "$SHA_FILE" ] || die "missing SHA file: $SHA_FILE"
[ -f "$REC" ] || die "missing receipt: $REC"
[ -f "$PUB" ] || die "missing seller pubkey: $PUB"

H1=$(sha256sum "$TAR" | cut -d" " -f1)
H2=$(head -n1 "$SHA_FILE" | tr -d "\r" | cut -d" " -f1)
H3=$(sed -n "s/.*\"sha256\":\"\\([^\"]*\\)\".*/\\1/p" "$REC" | head -n1 | tr -d "\r")
[ "$H1" = "$H2" ] || die "sha mismatch (*.sha256)"
[ "$H1" = "$H3" ] || die "sha mismatch (receipt.json)"

# Pull base64 signature from receipt (seller_sig must start with ed25519_openssl:)
SIGB64=$(sed -n "s/.*\"seller_sig\":\"ed25519_openssl:\\([^\"]*\\)\".*/\\1/p" "$REC" | head -n1 | tr -d "\r")
[ -n "$SIGB64" ] || die "no ed25519_openssl signature in receipt"
SIGDER="$(mktemp)"; printf "%s" "$SIGB64" | openssl base64 -d -A > "$SIGDER"

# Verify Ed25519 signature over the tar bytes
openssl pkeyutl -verify -pubin -inkey "$PUB" -rawin -sigfile "$SIGDER" -in "$TAR" >/dev/null \
  || die "ed25519 signature verify failed"

echo "OK: sha256 matches (*.sha256 + receipt) and ed25519 signature verifies." 
