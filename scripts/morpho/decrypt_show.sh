#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
enc="${1:-}"
LED1="analysis/morpho/ledger/morpho_receipts.jsonl"
LED2="analysis/morpho/ledger/secure_ledger.jsonl"
if [ -z "$enc" ]; then enc=$(ls -1t .secrets/*.tar.enc 2>/dev/null | head -n1); fi
[ -f "$enc" ] || { echo "[err] could not find encrypted blob (.secrets/*.tar.enc)"; exit 3; }
sha(){ openssl dgst -sha256 "$1" | awk "{print \$2}"; }
enc_sha_local="$(sha "$enc")"
enc_base="$(basename "$enc")"
line=""; [ -s "$LED1" ] && line="$(grep -F "\"enc_file\":\"$enc_base\"" "$LED1" 2>/dev/null | tail -n1)"
[ -z "$line" ] && [ -s "$LED2" ] && line="$(grep -F "\"enc_file\":\"$enc_base\"" "$LED2" 2>/dev/null | tail -n1)"
if [ -z "$line" ]; then
  [ -s "$LED2" ] && line="$(awk 'NF{L=$0} END{print L}' "$LED2")"
  [ -z "$line" ] && [ -s "$LED1" ] && line="$(awk 'NF{L=$0} END{print L}' "$LED1")"
fi
enc_sha_led="$(printf "%s" "$line" | sed -n 's/.*"enc_sha256":"\([^"]*\)".*/\1/p')"
echo "[info] enc file      : $enc"
echo "[info] local sha256 : $enc_sha_local"
echo "[info] ledger sha256: ${enc_sha_led:-<absent>}"
[ -n "$enc_sha_led" ] && [ "$enc_sha_local" != "$enc_sha_led" ] && { echo "[err] sha256 mismatch vs ledger"; exit 4; }
[ -n "${MORPHO_PASSPHRASE:-}" ] || [ -n "${MORPHO_KEYFILE:-}" ] || { echo "[err] set MORPHO_PASSPHRASE or MORPHO_KEYFILE"; exit 5; }
dst="analysis/morpho/decrypted/decrypt_$(date -u +%Y%m%d_%H%M%S)"
mkdir -p "$dst"; tmp="$dst/raw.tar"
if [ -n "${MORPHO_KEYFILE:-}" ] && [ -f "$MORPHO_KEYFILE" ]; then
  openssl enc -d -aes-256-cbc -pbkdf2 -iter 200000 -in "$enc" -out "$tmp" -pass file:"$MORPHO_KEYFILE" || { echo "[err] decrypt failed (keyfile)"; exit 6; }
else
  openssl enc -d -aes-256-cbc -pbkdf2 -iter 200000 -in "$enc" -out "$tmp" -pass env:MORPHO_PASSPHRASE || { echo "[err] decrypt failed (passphrase)"; exit 7; }
fi
tar -xf "$tmp" -C "$dst" || { echo "[err] tar extract failed"; exit 8; }
rm -f "$tmp" 2>/dev/null || true
echo "[ok] decrypted to: $dst"
echo "[list]"; ls -1 "$dst" 2>/dev/null || true
for n in FACE.txt face2.txt; do [ -f "$dst/$n" ] && { echo "---------------- $n ----------------"; cat "$dst/$n"; echo ""; }; done
exit 0
