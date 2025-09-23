#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
root="analysis/morpho"; in="$root/input"; led="$root/ledger"; sec=".secrets"; th="$root/thumbs"
[ -d "$in" ] || { echo "[secure] no input dir: $in"; exit 2; }
shopt -s nullglob; imgs=("$in"/*); [ "${#imgs[@]}" -gt 0 ] || { echo "[secure] no images in $in"; exit 3; }
ts="$(date -u +%Y%m%d_%H%M%S)"; tarraw="$sec/morpho_raw_$ts.tar"; enc="$sec/morpho_raw_$ts.tar.enc"
mkdir -p "$sec" "$led" "$th"

# Optional quick thumbnails (requires ImageMagick; skip if missing)
if command -v magick >/dev/null 2>&1; then
  for f in "$in"/*; do b="$(basename "$f")"; magick "$f" -resize 480x480 -blur 0x2 "$th/${b%.*}_thumb.jpg" 2>/dev/null || true; done
fi

# Pack raw inputs
tar -cf "$tarraw" -C "$in" . || { echo "[secure] tar failed"; exit 4; }
raw_sha=$(openssl dgst -sha256 "$tarraw" | awk "{print \$2}")

# Encrypt with OpenSSL AES-256. Use MORPHO_PASSPHRASE or MORPHO_KEYFILE for non-interactive runs.
if [ -n "${MORPHO_KEYFILE:-}" ] && [ -f "$MORPHO_KEYFILE" ]; then
  openssl enc -aes-256-cbc -salt -pbkdf2 -iter 200000 -in "$tarraw" -out "$enc" -pass file:"$MORPHO_KEYFILE" || { echo "[secure] encrypt failed"; exit 5; }
elif [ -n "${MORPHO_PASSPHRASE:-}" ]; then
  openssl enc -aes-256-cbc -salt -pbkdf2 -iter 200000 -in "$tarraw" -out "$enc" -pass env:MORPHO_PASSPHRASE || { echo "[secure] encrypt failed"; exit 6; }
else
  echo "[secure] set MORPHO_PASSPHRASE or MORPHO_KEYFILE before running"; rm -f "$tarraw"; exit 7
fi

enc_sha=$(openssl dgst -sha256 "$enc" | awk "{print \$2}")
size_raw=$(wc -c < "$tarraw" 2>/dev/null || echo 0)
size_enc=$(wc -c < "$enc" 2>/dev/null || echo 0)

# Write a JSONL ledger entry with immutable facts (safe to commit)
L="$led/secure_ledger.jsonl"
printf "%s" "{" >> "$L"
printf "%s" "\"timestamp\":\"$ts\",\"raw_tar\":\"$(basename "$tarraw")\",\"raw_sha256\":\"$raw_sha\"," >> "$L"
printf "%s" "\"enc_file\":\"$(basename "$enc")\",\"enc_sha256\":\"$enc_sha\"," >> "$L"
printf "%s" "\"size_raw\":$size_raw,\"size_enc\":$size_enc}" >> "$L"
printf "%s\n" "" >> "$L"

echo "[secure] stored: $enc (sha256=$enc_sha)"; echo "[secure] ledger appended: $L"; echo "[secure] keep your key material OFF-REPO."
